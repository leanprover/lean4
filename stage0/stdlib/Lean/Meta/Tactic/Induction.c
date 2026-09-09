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
size_t v_x_7610__boxed_361_; size_t v_x_7611__boxed_362_; lean_object* v_res_363_; 
v_x_7610__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_x_7611__boxed_362_ = lean_unbox_usize(v_x_358_);
lean_dec(v_x_358_);
v_res_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_356_, v_x_7610__boxed_361_, v_x_7611__boxed_362_, v_x_359_, v_x_360_);
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
v___x_487_ = lean_st_ref_put(v___y_448_, v___x_486_);
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
uint8_t v___y_574_; lean_object* v___y_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; uint8_t v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; lean_object* v___y_660_; uint8_t v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_whnfForall(v_recursorType_565_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; uint8_t v___y_836_; uint8_t v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; uint8_t v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; uint8_t v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; uint8_t v___x_936_; uint8_t v___y_938_; uint8_t v___x_985_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_936_ = lean_nat_dec_le(v_numMinors_561_, v_minorIdx_563_);
v___x_985_ = l_Lean_Expr_isForall(v_a_749_);
if (v___x_985_ == 0)
{
v___y_938_ = v___x_985_;
goto v___jp_937_;
}
else
{
lean_object* v_numArgs_986_; uint8_t v___x_987_; 
v_numArgs_986_ = lean_ctor_get(v_recursorInfo_555_, 3);
v___x_987_ = lean_nat_dec_lt(v_pos_562_, v_numArgs_986_);
v___y_938_ = v___x_987_;
goto v___jp_937_;
}
v___jp_750_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_754_, v___y_758_, v___y_759_, v___y_752_, v___y_763_, v___y_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
lean_inc(v_mvarId_553_);
v___x_767_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_749_, v_a_766_, v___y_759_, v___y_752_, v___y_763_, v___y_762_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_toCold_768_; lean_object* v_options_769_; lean_object* v_a_770_; lean_object* v_inheritedTraceOptions_771_; uint8_t v_hasTrace_772_; lean_object* v___x_773_; 
v_toCold_768_ = lean_ctor_get(v___y_763_, 0);
v_options_769_ = lean_ctor_get(v_toCold_768_, 2);
v_a_770_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_767_, 1);
v_inheritedTraceOptions_771_ = lean_ctor_get(v_toCold_768_, 11);
v_hasTrace_772_ = lean_ctor_get_uint8(v_options_769_, sizeof(void*)*1);
lean_inc(v_a_766_);
v___x_773_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_766_);
if (v_hasTrace_772_ == 0)
{
v___y_660_ = v___y_756_;
v___y_661_ = v___y_757_;
v___y_662_ = v___y_760_;
v___y_663_ = v___y_761_;
v___y_664_ = v___y_751_;
v___y_665_ = v_a_766_;
v___y_666_ = v_a_770_;
v___y_667_ = v___y_764_;
v___y_668_ = v___y_755_;
v___y_669_ = v___y_753_;
v___y_670_ = v___x_773_;
v___y_671_ = v___y_759_;
v___y_672_ = v___y_752_;
v___y_673_ = v___y_763_;
v___y_674_ = v___y_762_;
goto v___jp_659_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_771_, v_options_769_, v___x_775_);
if (v___x_776_ == 0)
{
v___y_660_ = v___y_756_;
v___y_661_ = v___y_757_;
v___y_662_ = v___y_760_;
v___y_663_ = v___y_761_;
v___y_664_ = v___y_751_;
v___y_665_ = v_a_766_;
v___y_666_ = v_a_770_;
v___y_667_ = v___y_764_;
v___y_668_ = v___y_755_;
v___y_669_ = v___y_753_;
v___y_670_ = v___x_773_;
v___y_671_ = v___y_759_;
v___y_672_ = v___y_752_;
v___y_673_ = v___y_763_;
v___y_674_ = v___y_762_;
goto v___jp_659_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_778_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_779_ = l_Lean_MessageData_ofName(v___x_778_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_774_, v___x_780_, v___y_759_, v___y_752_, v___y_763_, v___y_762_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_dec_ref_known(v___x_781_, 1);
v___y_660_ = v___y_756_;
v___y_661_ = v___y_757_;
v___y_662_ = v___y_760_;
v___y_663_ = v___y_761_;
v___y_664_ = v___y_751_;
v___y_665_ = v_a_766_;
v___y_666_ = v_a_770_;
v___y_667_ = v___y_764_;
v___y_668_ = v___y_755_;
v___y_669_ = v___y_753_;
v___y_670_ = v___x_773_;
v___y_671_ = v___y_759_;
v___y_672_ = v___y_752_;
v___y_673_ = v___y_763_;
v___y_674_ = v___y_762_;
goto v___jp_659_;
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v___x_773_);
lean_dec(v_a_770_);
lean_dec(v_a_766_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_761_);
lean_dec(v___y_756_);
lean_dec(v___y_755_);
lean_dec(v___y_751_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_a_766_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_761_);
lean_dec(v___y_756_);
lean_dec(v___y_755_);
lean_dec(v___y_751_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_790_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_767_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_767_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v___y_764_);
lean_dec(v___y_761_);
lean_dec(v___y_756_);
lean_dec(v___y_755_);
lean_dec(v___y_751_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_798_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_765_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_765_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
v___jp_806_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_817_ = lean_nat_sub(v___y_808_, v_initialArity_560_);
lean_dec(v___y_808_);
v___x_818_ = lean_array_get_size(v_reverted_556_);
v___x_819_ = lean_array_get_size(v_indices_558_);
v___x_820_ = lean_nat_sub(v___x_818_, v___x_819_);
v___x_821_ = lean_nat_sub(v___x_820_, v___y_812_);
lean_dec(v___x_820_);
v___x_822_ = lean_array_get_size(v_givenNames_554_);
v___x_823_ = lean_nat_dec_lt(v_minorIdx_563_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_box(0);
v___x_825_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*1, v___x_823_);
v___y_751_ = v___x_821_;
v___y_752_ = v___y_814_;
v___y_753_ = v___y_812_;
v___y_754_ = v___y_811_;
v___y_755_ = v___x_817_;
v___y_756_ = v___x_818_;
v___y_757_ = v___y_807_;
v___y_758_ = v___y_810_;
v___y_759_ = v___y_813_;
v___y_760_ = v___y_809_;
v___y_761_ = v___x_819_;
v___y_762_ = v___y_816_;
v___y_763_ = v___y_815_;
v___y_764_ = v___x_825_;
goto v___jp_750_;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = lean_array_fget_borrowed(v_givenNames_554_, v_minorIdx_563_);
lean_inc(v___x_826_);
v___y_751_ = v___x_821_;
v___y_752_ = v___y_814_;
v___y_753_ = v___y_812_;
v___y_754_ = v___y_811_;
v___y_755_ = v___x_817_;
v___y_756_ = v___x_818_;
v___y_757_ = v___y_807_;
v___y_758_ = v___y_810_;
v___y_759_ = v___y_813_;
v___y_760_ = v___y_809_;
v___y_761_ = v___x_819_;
v___y_762_ = v___y_816_;
v___y_763_ = v___y_815_;
v___y_764_ = v___x_826_;
goto v___jp_750_;
}
}
v___jp_827_:
{
if (v___y_836_ == 0)
{
lean_object* v___x_837_; uint8_t v___x_838_; 
lean_inc_ref(v___y_835_);
v___x_837_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_835_);
v___x_838_ = lean_nat_dec_lt(v___x_837_, v_initialArity_560_);
if (v___x_838_ == 0)
{
v___y_807_ = v___y_828_;
v___y_808_ = v___x_837_;
v___y_809_ = v___y_836_;
v___y_810_ = v___y_831_;
v___y_811_ = v___y_835_;
v___y_812_ = v___y_834_;
v___y_813_ = v___y_830_;
v___y_814_ = v___y_833_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_832_;
goto v___jp_806_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_841_ = l_Lean_Meta_throwTacticEx___redArg(v___x_839_, v_mvarId_553_, v___x_840_, v___y_830_, v___y_833_, v___y_829_, v___y_832_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec_ref_known(v___x_841_, 1);
v___y_807_ = v___y_828_;
v___y_808_ = v___x_837_;
v___y_809_ = v___y_836_;
v___y_810_ = v___y_831_;
v___y_811_ = v___y_835_;
v___y_812_ = v___y_834_;
v___y_813_ = v___y_830_;
v___y_814_ = v___y_833_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_832_;
goto v___jp_806_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v___x_837_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_831_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_box(0);
lean_inc_ref(v___y_835_);
v___x_851_ = l_Lean_Meta_synthInstance_x3f(v___y_835_, v___x_850_, v___y_830_, v___y_833_, v___y_829_, v___y_832_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
if (lean_obj_tag(v_a_852_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_835_, v___y_831_, v___y_830_, v___y_833_, v___y_829_, v___y_832_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
lean_inc(v_mvarId_553_);
v___x_855_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_749_, v_a_854_, v___y_830_, v___y_833_, v___y_829_, v___y_832_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
lean_inc(v_a_854_);
v___x_857_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_854_);
v___x_858_ = lean_nat_add(v_pos_562_, v___y_834_);
lean_dec(v_pos_562_);
v___x_859_ = lean_nat_add(v_minorIdx_563_, v___y_834_);
lean_dec(v_minorIdx_563_);
v___x_860_ = l_Lean_Expr_mvarId_x21(v_a_854_);
lean_dec(v_a_854_);
v___x_861_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_862_ = lean_box(0);
v___x_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_863_, 0, v___x_860_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
v___x_864_ = lean_array_push(v_subgoals_567_, v___x_863_);
v_pos_562_ = v___x_858_;
v_minorIdx_563_ = v___x_859_;
v_recursor_564_ = v___x_857_;
v_recursorType_565_ = v_a_856_;
v_subgoals_567_ = v___x_864_;
v_a_568_ = v___y_830_;
v_a_569_ = v___y_833_;
v_a_570_ = v___y_829_;
v_a_571_ = v___y_832_;
goto _start;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_854_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_866_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_855_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_855_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_874_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_853_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_853_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_val_882_; lean_object* v___x_883_; 
lean_dec_ref(v___y_835_);
lean_dec(v___y_831_);
v_val_882_ = lean_ctor_get(v_a_852_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_a_852_, 1);
lean_inc(v_mvarId_553_);
v___x_883_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_749_, v_val_882_, v___y_830_, v___y_833_, v___y_829_, v___y_832_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Expr_app___override(v_recursor_564_, v_val_882_);
v___x_886_ = lean_nat_add(v_pos_562_, v___y_834_);
lean_dec(v_pos_562_);
v___x_887_ = lean_nat_add(v_minorIdx_563_, v___y_834_);
lean_dec(v_minorIdx_563_);
v_pos_562_ = v___x_886_;
v_minorIdx_563_ = v___x_887_;
v_recursor_564_ = v___x_885_;
v_recursorType_565_ = v_a_884_;
v_a_568_ = v___y_830_;
v_a_569_ = v___y_833_;
v_a_570_ = v___y_829_;
v_a_571_ = v___y_832_;
goto _start;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_val_882_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_889_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_883_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_883_);
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
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v___y_835_);
lean_dec(v___y_831_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_897_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_851_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_851_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
v___jp_905_:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_BinderInfo_isInstImplicit(v___y_909_);
if (v___x_915_ == 0)
{
v___y_828_ = v___y_906_;
v___y_829_ = v___y_908_;
v___y_830_ = v___y_907_;
v___y_831_ = v___y_914_;
v___y_832_ = v___y_910_;
v___y_833_ = v___y_911_;
v___y_834_ = v___y_913_;
v___y_835_ = v___y_912_;
v___y_836_ = v___x_915_;
goto v___jp_827_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_array_get_size(v_givenNames_554_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_nat_dec_eq(v___x_916_, v___x_917_);
v___y_828_ = v___y_906_;
v___y_829_ = v___y_908_;
v___y_830_ = v___y_907_;
v___y_831_ = v___y_914_;
v___y_832_ = v___y_910_;
v___y_833_ = v___y_911_;
v___y_834_ = v___y_913_;
v___y_835_ = v___y_912_;
v___y_836_ = v___x_918_;
goto v___jp_827_;
}
}
v___jp_919_:
{
if (lean_obj_tag(v_a_749_) == 7)
{
lean_object* v_binderName_926_; lean_object* v_binderType_927_; uint8_t v_binderInfo_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_binderName_926_ = lean_ctor_get(v_a_749_, 0);
v_binderType_927_ = lean_ctor_get(v_a_749_, 1);
v_binderInfo_928_ = lean_ctor_get_uint8(v_a_749_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_927_);
v___x_929_ = l_Lean_Expr_headBeta(v_binderType_927_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_dec_eq(v_numMinors_561_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Lean_Name_eraseMacroScopes(v_binderName_926_);
v___x_933_ = l_Lean_Name_append(v___y_921_, v___x_932_);
v___y_906_ = v___y_920_;
v___y_907_ = v___y_922_;
v___y_908_ = v___y_924_;
v___y_909_ = v_binderInfo_928_;
v___y_910_ = v___y_925_;
v___y_911_ = v___y_923_;
v___y_912_ = v___x_929_;
v___y_913_ = v___x_930_;
v___y_914_ = v___x_933_;
goto v___jp_905_;
}
else
{
v___y_906_ = v___y_920_;
v___y_907_ = v___y_922_;
v___y_908_ = v___y_924_;
v___y_909_ = v_binderInfo_928_;
v___y_910_ = v___y_925_;
v___y_911_ = v___y_923_;
v___y_912_ = v___x_929_;
v___y_913_ = v___x_930_;
v___y_914_ = v___y_921_;
goto v___jp_905_;
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v___y_921_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v___x_934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_935_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_934_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_935_;
}
}
v___jp_937_:
{
if (v___y_938_ == 0)
{
lean_dec(v_a_749_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
if (v_consumedMajor_566_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_941_ = l_Lean_Meta_throwTacticEx___redArg(v___x_939_, v_mvarId_553_, v___x_940_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_dec_ref_known(v___x_941_, 1);
v___y_692_ = v_a_568_;
v___y_693_ = v_a_569_;
v___y_694_ = v_a_570_;
v___y_695_ = v_a_571_;
goto v___jp_691_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_mvarId_553_);
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
v___y_692_ = v_a_568_;
v___y_693_ = v_a_569_;
v___y_694_ = v_a_570_;
v___y_695_ = v_a_571_;
goto v___jp_691_;
}
}
else
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_555_);
v___x_951_ = lean_nat_dec_eq(v_pos_562_, v___x_950_);
lean_dec(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_inc(v_mvarId_553_);
v___x_952_ = l_Lean_MVarId_getTag(v_mvarId_553_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_952_) == 0)
{
if (v___x_936_ == 0)
{
lean_object* v_a_953_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___y_920_ = v___y_938_;
v___y_921_ = v_a_953_;
v___y_922_ = v_a_568_;
v___y_923_ = v_a_569_;
v___y_924_ = v_a_570_;
v___y_925_ = v_a_571_;
goto v___jp_919_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_952_, 1);
v___x_955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_957_ = l_Lean_Meta_throwTacticEx___redArg(v___x_955_, v_mvarId_553_, v___x_956_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_dec_ref_known(v___x_957_, 1);
v___y_920_ = v___y_938_;
v___y_921_ = v_a_954_;
v___y_922_ = v_a_568_;
v___y_923_ = v_a_569_;
v___y_924_ = v_a_570_;
v___y_925_ = v_a_571_;
goto v___jp_919_;
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_a_954_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_966_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_952_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_952_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_array_get_size(v_indices_558_);
v___x_976_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
v___y_574_ = v___x_951_;
v___y_575_ = v___x_975_;
v_fst_576_ = v_recursor_564_;
v_snd_577_ = v_a_749_;
goto v___jp_573_;
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; 
lean_inc(v_a_749_);
lean_inc_ref(v_recursor_564_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_recursor_564_);
lean_ctor_set(v___x_977_, 1, v_a_749_);
v___x_978_ = lean_nat_dec_le(v___x_975_, v___x_975_);
if (v___x_978_ == 0)
{
if (v___x_976_ == 0)
{
lean_dec_ref_known(v___x_977_, 2);
v___y_574_ = v___x_951_;
v___y_575_ = v___x_975_;
v_fst_576_ = v_recursor_564_;
v_snd_577_ = v_a_749_;
goto v___jp_573_;
}
else
{
size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
lean_dec(v_a_749_);
lean_dec_ref(v_recursor_564_);
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_975_);
lean_inc(v_mvarId_553_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_979_, v___x_980_, v___x_977_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_594_ = v___x_951_;
v___y_595_ = v___x_975_;
v___y_596_ = v___x_981_;
goto v___jp_593_;
}
}
else
{
size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
lean_dec(v_a_749_);
lean_dec_ref(v_recursor_564_);
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_975_);
lean_inc(v_mvarId_553_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_982_, v___x_983_, v___x_977_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_594_ = v___x_951_;
v___y_595_ = v___x_975_;
v___y_596_ = v___x_984_;
goto v___jp_593_;
}
}
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_988_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_748_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_748_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
v___jp_573_:
{
lean_object* v___x_578_; 
lean_inc(v_mvarId_553_);
v___x_578_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_snd_577_, v_major_557_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
lean_inc_ref(v_major_557_);
v___x_580_ = l_Lean_Expr_app___override(v_fst_576_, v_major_557_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_pos_562_, v___x_581_);
lean_dec(v_pos_562_);
v___x_583_ = lean_nat_add(v___x_582_, v___y_575_);
lean_dec(v___y_575_);
lean_dec(v___x_582_);
v_pos_562_ = v___x_583_;
v_recursor_564_ = v___x_580_;
v_recursorType_565_ = v_a_579_;
v_consumedMajor_566_ = v___y_574_;
goto _start;
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_fst_576_);
lean_dec(v___y_575_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_585_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_578_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
v___jp_593_:
{
if (lean_obj_tag(v___y_596_) == 0)
{
lean_object* v_a_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; 
v_a_597_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___y_596_, 1);
v_fst_598_ = lean_ctor_get(v_a_597_, 0);
lean_inc(v_fst_598_);
v_snd_599_ = lean_ctor_get(v_a_597_, 1);
lean_inc(v_snd_599_);
lean_dec(v_a_597_);
v___y_574_ = v___y_594_;
v___y_575_ = v___y_595_;
v_fst_576_ = v_fst_598_;
v_snd_577_ = v_snd_599_;
goto v___jp_573_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v___y_595_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_600_ = lean_ctor_get(v___y_596_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___y_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___y_596_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___y_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
v___jp_608_:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Meta_introNCore(v___y_622_, v___y_617_, v___y_612_, v___y_624_, v___y_620_, v___y_614_, v___y_610_, v___y_623_, v___y_611_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v_fst_627_ = lean_ctor_get(v_a_626_, 0);
lean_inc(v_fst_627_);
v_snd_628_ = lean_ctor_get(v_a_626_, 1);
lean_inc(v_snd_628_);
lean_dec(v_a_626_);
v___x_629_ = lean_box(0);
v___x_630_ = l_Lean_Meta_introNCore(v_snd_628_, v___y_609_, v___x_629_, v___y_620_, v___y_618_, v___y_614_, v___y_610_, v___y_623_, v___y_611_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; size_t v_sz_635_; size_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v_fst_632_ = lean_ctor_get(v_a_631_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_a_631_, 1);
lean_inc(v_snd_633_);
lean_dec(v_a_631_);
lean_inc(v_baseSubst_559_);
lean_inc(v___y_619_);
v___x_634_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_621_, v_reverted_556_, v_fst_632_, v___y_619_, v___y_619_, v_baseSubst_559_);
lean_dec(v___y_619_);
lean_dec(v_fst_632_);
lean_dec(v___y_621_);
v_sz_635_ = lean_array_size(v_fst_627_);
v___x_636_ = ((size_t)0ULL);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_635_, v___x_636_, v_fst_627_);
v___x_638_ = lean_nat_add(v_pos_562_, v___y_616_);
lean_dec(v_pos_562_);
v___x_639_ = lean_nat_add(v_minorIdx_563_, v___y_616_);
lean_dec(v_minorIdx_563_);
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v_snd_633_);
lean_ctor_set(v___x_640_, 1, v___x_637_);
lean_ctor_set(v___x_640_, 2, v___x_634_);
v___x_641_ = lean_array_push(v_subgoals_567_, v___x_640_);
v_pos_562_ = v___x_638_;
v_minorIdx_563_ = v___x_639_;
v_recursor_564_ = v___y_615_;
v_recursorType_565_ = v___y_613_;
v_subgoals_567_ = v___x_641_;
v_a_568_ = v___y_614_;
v_a_569_ = v___y_610_;
v_a_570_ = v___y_623_;
v_a_571_ = v___y_611_;
goto _start;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_fst_627_);
lean_dec(v___y_621_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v___y_613_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_643_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_630_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_630_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v___y_621_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_609_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_651_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_625_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_625_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_Expr_mvarId_x21(v___y_665_);
lean_dec_ref(v___y_665_);
v___x_676_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_677_ = l_Lean_MVarId_tryClear(v___x_675_, v___x_676_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
uint8_t v_explicit_678_; 
v_explicit_678_ = lean_ctor_get_uint8(v___y_667_, sizeof(void*)*1);
if (v_explicit_678_ == 0)
{
lean_object* v_a_679_; lean_object* v_varNames_680_; 
v_a_679_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_677_, 1);
v_varNames_680_ = lean_ctor_get(v___y_667_, 0);
lean_inc(v_varNames_680_);
lean_dec_ref(v___y_667_);
v___y_609_ = v___y_664_;
v___y_610_ = v___y_672_;
v___y_611_ = v___y_674_;
v___y_612_ = v_varNames_680_;
v___y_613_ = v___y_666_;
v___y_614_ = v___y_671_;
v___y_615_ = v___y_670_;
v___y_616_ = v___y_669_;
v___y_617_ = v___y_668_;
v___y_618_ = v___y_661_;
v___y_619_ = v___y_660_;
v___y_620_ = v___y_662_;
v___y_621_ = v___y_663_;
v___y_622_ = v_a_679_;
v___y_623_ = v___y_673_;
v___y_624_ = v___y_661_;
goto v___jp_608_;
}
else
{
lean_object* v_a_681_; lean_object* v_varNames_682_; 
v_a_681_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_677_, 1);
v_varNames_682_ = lean_ctor_get(v___y_667_, 0);
lean_inc(v_varNames_682_);
lean_dec_ref(v___y_667_);
v___y_609_ = v___y_664_;
v___y_610_ = v___y_672_;
v___y_611_ = v___y_674_;
v___y_612_ = v_varNames_682_;
v___y_613_ = v___y_666_;
v___y_614_ = v___y_671_;
v___y_615_ = v___y_670_;
v___y_616_ = v___y_669_;
v___y_617_ = v___y_668_;
v___y_618_ = v___y_661_;
v___y_619_ = v___y_660_;
v___y_620_ = v___y_662_;
v___y_621_ = v___y_663_;
v___y_622_ = v_a_681_;
v___y_623_ = v___y_673_;
v___y_624_ = v___y_662_;
goto v___jp_608_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v___y_670_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec(v___y_660_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_683_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_677_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_677_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
v___jp_691_:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_553_, v_recursor_564_, v___y_693_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_738_; 
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_739_);
v___x_698_ = v___x_696_;
v_isShared_699_ = v_isSharedCheck_738_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_696_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_738_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_toCold_700_; lean_object* v_options_701_; uint8_t v_hasTrace_702_; 
v_toCold_700_ = lean_ctor_get(v___y_694_, 0);
v_options_701_ = lean_ctor_get(v_toCold_700_, 2);
v_hasTrace_702_ = lean_ctor_get_uint8(v_options_701_, sizeof(void*)*1);
if (v_hasTrace_702_ == 0)
{
lean_object* v___x_704_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_subgoals_567_);
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_subgoals_567_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v_inheritedTraceOptions_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_inheritedTraceOptions_706_ = lean_ctor_get(v_toCold_700_, 11);
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_706_, v_options_701_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_711_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_subgoals_567_);
v___x_711_ = v___x_698_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_subgoals_567_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_del_object(v___x_698_);
v___x_713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_714_ = lean_array_get_size(v_subgoals_567_);
v___x_715_ = l_Nat_reprFast(v___x_714_);
v___x_716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = l_Lean_MessageData_ofFormat(v___x_716_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_713_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_707_, v___x_720_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_729_);
v___x_723_ = v___x_721_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_dec(v___x_721_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_subgoals_567_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_subgoals_567_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_subgoals_567_);
v_a_730_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_721_);
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
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v_subgoals_567_);
v_a_740_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_696_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_696_);
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
lean_object* v_mvarId_996_ = _args[0];
lean_object* v_givenNames_997_ = _args[1];
lean_object* v_recursorInfo_998_ = _args[2];
lean_object* v_reverted_999_ = _args[3];
lean_object* v_major_1000_ = _args[4];
lean_object* v_indices_1001_ = _args[5];
lean_object* v_baseSubst_1002_ = _args[6];
lean_object* v_initialArity_1003_ = _args[7];
lean_object* v_numMinors_1004_ = _args[8];
lean_object* v_pos_1005_ = _args[9];
lean_object* v_minorIdx_1006_ = _args[10];
lean_object* v_recursor_1007_ = _args[11];
lean_object* v_recursorType_1008_ = _args[12];
lean_object* v_consumedMajor_1009_ = _args[13];
lean_object* v_subgoals_1010_ = _args[14];
lean_object* v_a_1011_ = _args[15];
lean_object* v_a_1012_ = _args[16];
lean_object* v_a_1013_ = _args[17];
lean_object* v_a_1014_ = _args[18];
lean_object* v_a_1015_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1016_; lean_object* v_res_1017_; 
v_consumedMajor_boxed_1016_ = lean_unbox(v_consumedMajor_1009_);
v_res_1017_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_996_, v_givenNames_997_, v_recursorInfo_998_, v_reverted_999_, v_major_1000_, v_indices_1001_, v_baseSubst_1002_, v_initialArity_1003_, v_numMinors_1004_, v_pos_1005_, v_minorIdx_1006_, v_recursor_1007_, v_recursorType_1008_, v_consumedMajor_boxed_1016_, v_subgoals_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_numMinors_1004_);
lean_dec(v_initialArity_1003_);
lean_dec_ref(v_indices_1001_);
lean_dec_ref(v_reverted_999_);
lean_dec_ref(v_recursorInfo_998_);
lean_dec_ref(v_givenNames_997_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1018_, lean_object* v_val_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1018_, v_val_1019_, v___y_1021_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1026_, lean_object* v_val_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1026_, v_val_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1034_, lean_object* v_reverted_1035_, lean_object* v_fst_1036_, lean_object* v_n_1037_, lean_object* v_j_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1034_, v_reverted_1035_, v_fst_1036_, v_n_1037_, v_j_1038_, v_a_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1042_, lean_object* v_reverted_1043_, lean_object* v_fst_1044_, lean_object* v_n_1045_, lean_object* v_j_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1042_, v_reverted_1043_, v_fst_1044_, v_n_1045_, v_j_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_n_1045_);
lean_dec_ref(v_fst_1044_);
lean_dec_ref(v_reverted_1043_);
lean_dec(v___x_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1051_, v_x_1052_, v_x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1055_, lean_object* v_x_1056_, size_t v_x_1057_, size_t v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1056_, v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
size_t v_x_8964__boxed_1068_; size_t v_x_8965__boxed_1069_; lean_object* v_res_1070_; 
v_x_8964__boxed_1068_ = lean_unbox_usize(v_x_1064_);
lean_dec(v_x_1064_);
v_x_8965__boxed_1069_ = lean_unbox_usize(v_x_1065_);
lean_dec(v_x_1065_);
v_res_1070_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1062_, v_x_1063_, v_x_8964__boxed_1068_, v_x_8965__boxed_1069_, v_x_1066_, v_x_1067_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1071_, lean_object* v_n_1072_, lean_object* v_k_1073_, lean_object* v_v_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1072_, v_k_1073_, v_v_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1076_, size_t v_depth_1077_, lean_object* v_keys_1078_, lean_object* v_vals_1079_, lean_object* v_heq_1080_, lean_object* v_i_1081_, lean_object* v_entries_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1077_, v_keys_1078_, v_vals_1079_, v_i_1081_, v_entries_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_depth_1085_, lean_object* v_keys_1086_, lean_object* v_vals_1087_, lean_object* v_heq_1088_, lean_object* v_i_1089_, lean_object* v_entries_1090_){
_start:
{
size_t v_depth_boxed_1091_; lean_object* v_res_1092_; 
v_depth_boxed_1091_ = lean_unbox_usize(v_depth_1085_);
lean_dec(v_depth_1085_);
v_res_1092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1084_, v_depth_boxed_1091_, v_keys_1086_, v_vals_1087_, v_heq_1088_, v_i_1089_, v_entries_1090_);
lean_dec_ref(v_vals_1087_);
lean_dec_ref(v_keys_1086_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1094_, v_x_1095_, v_x_1096_, v_x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1101_, lean_object* v_givenNames_1102_, lean_object* v_recursorInfo_1103_, lean_object* v_reverted_1104_, lean_object* v_major_1105_, lean_object* v_indices_1106_, lean_object* v_baseSubst_1107_, lean_object* v_recursor_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
lean_inc(v_mvarId_1101_);
v___x_1114_ = l_Lean_MVarId_getType(v_mvarId_1101_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc_ref(v_recursor_1108_);
v___x_1116_ = lean_infer_type(v_recursor_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v_paramsPos_1118_; lean_object* v_produceMotive_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v_paramsPos_1118_ = lean_ctor_get(v_recursorInfo_1103_, 5);
v_produceMotive_1119_ = lean_ctor_get(v_recursorInfo_1103_, 7);
v___x_1120_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1115_);
v___x_1121_ = l_List_lengthTR___redArg(v_produceMotive_1119_);
v___x_1122_ = l_List_lengthTR___redArg(v_paramsPos_1118_);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_nat_add(v___x_1122_, v___x_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = 0;
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1128_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1101_, v_givenNames_1102_, v_recursorInfo_1103_, v_reverted_1104_, v_major_1105_, v_indices_1106_, v_baseSubst_1107_, v___x_1120_, v___x_1121_, v___x_1124_, v___x_1125_, v_recursor_1108_, v_a_1117_, v___x_1126_, v___x_1127_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v___x_1121_);
lean_dec(v___x_1120_);
return v___x_1128_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_a_1115_);
lean_dec_ref(v_recursor_1108_);
lean_dec(v_baseSubst_1107_);
lean_dec_ref(v_major_1105_);
lean_dec(v_mvarId_1101_);
v_a_1129_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1116_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1116_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_recursor_1108_);
lean_dec(v_baseSubst_1107_);
lean_dec_ref(v_major_1105_);
lean_dec(v_mvarId_1101_);
v_a_1137_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1114_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1114_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1145_, lean_object* v_givenNames_1146_, lean_object* v_recursorInfo_1147_, lean_object* v_reverted_1148_, lean_object* v_major_1149_, lean_object* v_indices_1150_, lean_object* v_baseSubst_1151_, lean_object* v_recursor_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1145_, v_givenNames_1146_, v_recursorInfo_1147_, v_reverted_1148_, v_major_1149_, v_indices_1150_, v_baseSubst_1151_, v_recursor_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec_ref(v_indices_1150_);
lean_dec_ref(v_reverted_1148_);
lean_dec_ref(v_recursorInfo_1147_);
lean_dec_ref(v_givenNames_1146_);
return v_res_1158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1162_, lean_object* v_mvarId_1163_, lean_object* v_majorType_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1171_ = l_Lean_indentExpr(v_majorType_1164_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1162_, v_mvarId_1163_, v___x_1173_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1175_, lean_object* v_mvarId_1176_, lean_object* v_majorType_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1175_, v_mvarId_1176_, v_majorType_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1184_, lean_object* v_tacticName_1185_, lean_object* v_mvarId_1186_, lean_object* v_majorType_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1185_, v_mvarId_1186_, v_majorType_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_tacticName_1195_, lean_object* v_mvarId_1196_, lean_object* v_majorType_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1194_, v_tacticName_1195_, v_mvarId_1196_, v_majorType_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1204_, lean_object* v_x_1205_){
_start:
{
uint8_t v___x_1206_; 
v___x_1206_ = l_Lean_instBEqFVarId_beq(v_fvarId_1204_, v_x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1207_, lean_object* v_x_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1207_, v_x_1208_);
lean_dec(v_x_1208_);
lean_dec(v_fvarId_1207_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1213_);
lean_dec(v_x_1213_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_unsigned_to_nat(16u);
v___x_1219_ = lean_mk_array(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1223_, lean_object* v_fvarId_1224_, uint8_t v_generalizeNondepLet_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___y_1249_; lean_object* v___f_1253_; lean_object* v___f_1254_; 
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1253_, 0, v_fvarId_1224_);
v___f_1254_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1223_) == 0)
{
lean_object* v_type_1255_; lean_object* v___x_1256_; uint8_t v_fst_1258_; lean_object* v_mctx_1259_; lean_object* v___y_1277_; lean_object* v_mctx_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_type_1255_ = lean_ctor_get(v_localDecl_1223_, 3);
lean_inc_ref(v_type_1255_);
lean_dec_ref_known(v_localDecl_1223_, 4);
v___x_1256_ = lean_st_ref_get(v___y_1226_);
v_mctx_1282_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref_n(v_mctx_1282_, 2);
lean_dec(v___x_1256_);
v___x_1283_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v_mctx_1282_);
v___x_1285_ = l_Lean_Expr_hasFVar(v_type_1255_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; 
v___x_1286_ = l_Lean_Expr_hasMVar(v_type_1255_);
if (v___x_1286_ == 0)
{
lean_dec_ref_known(v___x_1284_, 2);
lean_dec_ref(v_type_1255_);
lean_dec_ref(v___f_1253_);
v_fst_1258_ = v___x_1286_;
v_mctx_1259_ = v_mctx_1282_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1287_; 
lean_dec_ref(v_mctx_1282_);
v___x_1287_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1255_, v___x_1284_);
v___y_1277_ = v___x_1287_;
goto v___jp_1276_;
}
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_mctx_1282_);
v___x_1288_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1255_, v___x_1284_);
v___y_1277_ = v___x_1288_;
goto v___jp_1276_;
}
v___jp_1257_:
{
lean_object* v___x_1260_; lean_object* v_cache_1261_; lean_object* v_zetaDeltaFVarIds_1262_; lean_object* v_postponed_1263_; lean_object* v_diag_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1274_; 
v___x_1260_ = lean_st_ref_take(v___y_1226_);
v_cache_1261_ = lean_ctor_get(v___x_1260_, 1);
v_zetaDeltaFVarIds_1262_ = lean_ctor_get(v___x_1260_, 2);
v_postponed_1263_ = lean_ctor_get(v___x_1260_, 3);
v_diag_1264_ = lean_ctor_get(v___x_1260_, 4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1275_);
v___x_1266_ = v___x_1260_;
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_diag_1264_);
lean_inc(v_postponed_1263_);
lean_inc(v_zetaDeltaFVarIds_1262_);
lean_inc(v_cache_1261_);
lean_dec(v___x_1260_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_mctx_1259_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_mctx_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_cache_1261_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_zetaDeltaFVarIds_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_postponed_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_diag_1264_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_st_ref_put(v___y_1226_, v___x_1269_);
v___x_1271_ = lean_box(v_fst_1258_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
}
v___jp_1276_:
{
lean_object* v_snd_1278_; lean_object* v_fst_1279_; lean_object* v_mctx_1280_; uint8_t v___x_1281_; 
v_snd_1278_ = lean_ctor_get(v___y_1277_, 1);
lean_inc(v_snd_1278_);
v_fst_1279_ = lean_ctor_get(v___y_1277_, 0);
lean_inc(v_fst_1279_);
lean_dec_ref(v___y_1277_);
v_mctx_1280_ = lean_ctor_get(v_snd_1278_, 1);
lean_inc_ref(v_mctx_1280_);
lean_dec(v_snd_1278_);
v___x_1281_ = lean_unbox(v_fst_1279_);
lean_dec(v_fst_1279_);
v_fst_1258_ = v___x_1281_;
v_mctx_1259_ = v_mctx_1280_;
goto v___jp_1257_;
}
}
else
{
lean_object* v_type_1289_; lean_object* v_value_1290_; uint8_t v_nondep_1291_; uint8_t v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___y_1300_; 
v_type_1289_ = lean_ctor_get(v_localDecl_1223_, 3);
lean_inc_ref(v_type_1289_);
v_value_1290_ = lean_ctor_get(v_localDecl_1223_, 4);
lean_inc_ref(v_value_1290_);
v_nondep_1291_ = lean_ctor_get_uint8(v_localDecl_1223_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1223_, 5);
if (v_generalizeNondepLet_1225_ == 0)
{
goto v___jp_1304_;
}
else
{
if (v_nondep_1291_ == 0)
{
goto v___jp_1304_;
}
else
{
lean_object* v___x_1313_; uint8_t v_fst_1315_; lean_object* v_mctx_1316_; lean_object* v___y_1334_; lean_object* v_mctx_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
lean_dec_ref(v_value_1290_);
v___x_1313_ = lean_st_ref_get(v___y_1226_);
v_mctx_1339_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_ref_n(v_mctx_1339_, 2);
lean_dec(v___x_1313_);
v___x_1340_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_mctx_1339_);
v___x_1342_ = l_Lean_Expr_hasFVar(v_type_1289_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Expr_hasMVar(v_type_1289_);
if (v___x_1343_ == 0)
{
lean_dec_ref_known(v___x_1341_, 2);
lean_dec_ref(v_type_1289_);
lean_dec_ref(v___f_1253_);
v_fst_1315_ = v___x_1343_;
v_mctx_1316_ = v_mctx_1339_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v_mctx_1339_);
v___x_1344_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1341_);
v___y_1334_ = v___x_1344_;
goto v___jp_1333_;
}
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v_mctx_1339_);
v___x_1345_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1341_);
v___y_1334_ = v___x_1345_;
goto v___jp_1333_;
}
v___jp_1314_:
{
lean_object* v___x_1317_; lean_object* v_cache_1318_; lean_object* v_zetaDeltaFVarIds_1319_; lean_object* v_postponed_1320_; lean_object* v_diag_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v___x_1317_ = lean_st_ref_take(v___y_1226_);
v_cache_1318_ = lean_ctor_get(v___x_1317_, 1);
v_zetaDeltaFVarIds_1319_ = lean_ctor_get(v___x_1317_, 2);
v_postponed_1320_ = lean_ctor_get(v___x_1317_, 3);
v_diag_1321_ = lean_ctor_get(v___x_1317_, 4);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1317_, 0);
lean_dec(v_unused_1332_);
v___x_1323_ = v___x_1317_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_diag_1321_);
lean_inc(v_postponed_1320_);
lean_inc(v_zetaDeltaFVarIds_1319_);
lean_inc(v_cache_1318_);
lean_dec(v___x_1317_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_mctx_1316_);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_mctx_1316_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_cache_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_zetaDeltaFVarIds_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_postponed_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_diag_1321_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_st_ref_put(v___y_1226_, v___x_1326_);
v___x_1328_ = lean_box(v_fst_1315_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
}
v___jp_1333_:
{
lean_object* v_snd_1335_; lean_object* v_fst_1336_; lean_object* v_mctx_1337_; uint8_t v___x_1338_; 
v_snd_1335_ = lean_ctor_get(v___y_1334_, 1);
lean_inc(v_snd_1335_);
v_fst_1336_ = lean_ctor_get(v___y_1334_, 0);
lean_inc(v_fst_1336_);
lean_dec_ref(v___y_1334_);
v_mctx_1337_ = lean_ctor_get(v_snd_1335_, 1);
lean_inc_ref(v_mctx_1337_);
lean_dec(v_snd_1335_);
v___x_1338_ = lean_unbox(v_fst_1336_);
lean_dec(v_fst_1336_);
v_fst_1315_ = v___x_1338_;
v_mctx_1316_ = v_mctx_1337_;
goto v___jp_1314_;
}
}
}
v___jp_1292_:
{
if (v_fst_1293_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_hasFVar(v_value_1290_);
if (v___x_1295_ == 0)
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_Expr_hasMVar(v_value_1290_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_value_1290_);
lean_dec_ref(v___f_1253_);
v_fst_1229_ = v___x_1296_;
v_snd_1230_ = v_snd_1294_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_value_1290_, v_snd_1294_);
v___y_1249_ = v___x_1297_;
goto v___jp_1248_;
}
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_value_1290_, v_snd_1294_);
v___y_1249_ = v___x_1298_;
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v_value_1290_);
lean_dec_ref(v___f_1253_);
v_fst_1229_ = v_fst_1293_;
v_snd_1230_ = v_snd_1294_;
goto v___jp_1228_;
}
}
v___jp_1299_:
{
lean_object* v_fst_1301_; lean_object* v_snd_1302_; uint8_t v___x_1303_; 
v_fst_1301_ = lean_ctor_get(v___y_1300_, 0);
lean_inc(v_fst_1301_);
v_snd_1302_ = lean_ctor_get(v___y_1300_, 1);
lean_inc(v_snd_1302_);
lean_dec_ref(v___y_1300_);
v___x_1303_ = lean_unbox(v_fst_1301_);
lean_dec(v_fst_1301_);
v_fst_1293_ = v___x_1303_;
v_snd_1294_ = v_snd_1302_;
goto v___jp_1292_;
}
v___jp_1304_:
{
lean_object* v___x_1305_; lean_object* v_mctx_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1305_ = lean_st_ref_get(v___y_1226_);
v_mctx_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_mctx_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_mctx_1306_);
v___x_1309_ = l_Lean_Expr_hasFVar(v_type_1289_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Expr_hasMVar(v_type_1289_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v_type_1289_);
v_fst_1293_ = v___x_1310_;
v_snd_1294_ = v___x_1308_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1311_; 
lean_inc_ref(v___f_1253_);
v___x_1311_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1308_);
v___y_1300_ = v___x_1311_;
goto v___jp_1299_;
}
}
else
{
lean_object* v___x_1312_; 
lean_inc_ref(v___f_1253_);
v___x_1312_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1308_);
v___y_1300_ = v___x_1312_;
goto v___jp_1299_;
}
}
}
v___jp_1228_:
{
lean_object* v_mctx_1231_; lean_object* v___x_1232_; lean_object* v_cache_1233_; lean_object* v_zetaDeltaFVarIds_1234_; lean_object* v_postponed_1235_; lean_object* v_diag_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1246_; 
v_mctx_1231_ = lean_ctor_get(v_snd_1230_, 1);
lean_inc_ref(v_mctx_1231_);
lean_dec_ref(v_snd_1230_);
v___x_1232_ = lean_st_ref_take(v___y_1226_);
v_cache_1233_ = lean_ctor_get(v___x_1232_, 1);
v_zetaDeltaFVarIds_1234_ = lean_ctor_get(v___x_1232_, 2);
v_postponed_1235_ = lean_ctor_get(v___x_1232_, 3);
v_diag_1236_ = lean_ctor_get(v___x_1232_, 4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1247_);
v___x_1238_ = v___x_1232_;
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_diag_1236_);
lean_inc(v_postponed_1235_);
lean_inc(v_zetaDeltaFVarIds_1234_);
lean_inc(v_cache_1233_);
lean_dec(v___x_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v_mctx_1231_);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_mctx_1231_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_cache_1233_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_zetaDeltaFVarIds_1234_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_postponed_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_diag_1236_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_st_ref_put(v___y_1226_, v___x_1241_);
v___x_1243_ = lean_box(v_fst_1229_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
v___jp_1248_:
{
lean_object* v_fst_1250_; lean_object* v_snd_1251_; uint8_t v___x_1252_; 
v_fst_1250_ = lean_ctor_get(v___y_1249_, 0);
lean_inc(v_fst_1250_);
v_snd_1251_ = lean_ctor_get(v___y_1249_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v___y_1249_);
v___x_1252_ = lean_unbox(v_fst_1250_);
lean_dec(v_fst_1250_);
v_fst_1229_ = v___x_1252_;
v_snd_1230_ = v_snd_1251_;
goto v___jp_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1346_, lean_object* v_fvarId_1347_, lean_object* v_generalizeNondepLet_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1351_; lean_object* v_res_1352_; 
v_generalizeNondepLet_boxed_1351_ = lean_unbox(v_generalizeNondepLet_1348_);
v_res_1352_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1346_, v_fvarId_1347_, v_generalizeNondepLet_boxed_1351_, v___y_1349_);
lean_dec(v___y_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1353_, lean_object* v_fvarId_1354_, uint8_t v_generalizeNondepLet_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1353_, v_fvarId_1354_, v_generalizeNondepLet_1355_, v___y_1357_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1362_, lean_object* v_fvarId_1363_, lean_object* v_generalizeNondepLet_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1370_; lean_object* v_res_1371_; 
v_generalizeNondepLet_boxed_1370_ = lean_unbox(v_generalizeNondepLet_1364_);
v_res_1371_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1362_, v_fvarId_1363_, v_generalizeNondepLet_boxed_1370_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1372_, lean_object* v_fvarId_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; uint8_t v_fst_1378_; lean_object* v_mctx_1379_; lean_object* v___y_1397_; lean_object* v_mctx_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1376_ = lean_st_ref_get(v___y_1374_);
v_mctx_1402_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref_n(v_mctx_1402_, 2);
lean_dec(v___x_1376_);
v___f_1403_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1404_, 0, v_fvarId_1373_);
v___x_1405_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v_mctx_1402_);
v___x_1407_ = l_Lean_Expr_hasFVar(v_e_1372_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_Expr_hasMVar(v_e_1372_);
if (v___x_1408_ == 0)
{
lean_dec_ref_known(v___x_1406_, 2);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v_e_1372_);
v_fst_1378_ = v___x_1408_;
v_mctx_1379_ = v_mctx_1402_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1409_; 
lean_dec_ref(v_mctx_1402_);
v___x_1409_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1404_, v___f_1403_, v_e_1372_, v___x_1406_);
v___y_1397_ = v___x_1409_;
goto v___jp_1396_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec_ref(v_mctx_1402_);
v___x_1410_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1404_, v___f_1403_, v_e_1372_, v___x_1406_);
v___y_1397_ = v___x_1410_;
goto v___jp_1396_;
}
v___jp_1377_:
{
lean_object* v___x_1380_; lean_object* v_cache_1381_; lean_object* v_zetaDeltaFVarIds_1382_; lean_object* v_postponed_1383_; lean_object* v_diag_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v___x_1380_ = lean_st_ref_take(v___y_1374_);
v_cache_1381_ = lean_ctor_get(v___x_1380_, 1);
v_zetaDeltaFVarIds_1382_ = lean_ctor_get(v___x_1380_, 2);
v_postponed_1383_ = lean_ctor_get(v___x_1380_, 3);
v_diag_1384_ = lean_ctor_get(v___x_1380_, 4);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1380_, 0);
lean_dec(v_unused_1395_);
v___x_1386_ = v___x_1380_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_diag_1384_);
lean_inc(v_postponed_1383_);
lean_inc(v_zetaDeltaFVarIds_1382_);
lean_inc(v_cache_1381_);
lean_dec(v___x_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_mctx_1379_);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_mctx_1379_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_cache_1381_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_zetaDeltaFVarIds_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_postponed_1383_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_diag_1384_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_st_ref_put(v___y_1374_, v___x_1389_);
v___x_1391_ = lean_box(v_fst_1378_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
v___jp_1396_:
{
lean_object* v_snd_1398_; lean_object* v_fst_1399_; lean_object* v_mctx_1400_; uint8_t v___x_1401_; 
v_snd_1398_ = lean_ctor_get(v___y_1397_, 1);
lean_inc(v_snd_1398_);
v_fst_1399_ = lean_ctor_get(v___y_1397_, 0);
lean_inc(v_fst_1399_);
lean_dec_ref(v___y_1397_);
v_mctx_1400_ = lean_ctor_get(v_snd_1398_, 1);
lean_inc_ref(v_mctx_1400_);
lean_dec(v_snd_1398_);
v___x_1401_ = lean_unbox(v_fst_1399_);
lean_dec(v_fst_1399_);
v_fst_1378_ = v___x_1401_;
v_mctx_1379_ = v_mctx_1400_;
goto v___jp_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1411_, lean_object* v_fvarId_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1411_, v_fvarId_1412_, v___y_1413_);
lean_dec(v___y_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1416_, lean_object* v_fvarId_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1416_, v_fvarId_1417_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1424_, lean_object* v_fvarId_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1424_, v_fvarId_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1432_, lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
uint8_t v___x_1434_; 
v___x_1434_ = 0;
return v___x_1434_;
}
else
{
lean_object* v_head_1435_; lean_object* v_tail_1436_; uint8_t v___x_1437_; 
v_head_1435_ = lean_ctor_get(v_x_1433_, 0);
v_tail_1436_ = lean_ctor_get(v_x_1433_, 1);
v___x_1437_ = lean_nat_dec_eq(v_a_1432_, v_head_1435_);
if (v___x_1437_ == 0)
{
v_x_1433_ = v_tail_1436_;
goto _start;
}
else
{
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1439_, lean_object* v_x_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1439_, v_x_1440_);
lean_dec(v_x_1440_);
lean_dec(v_a_1439_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1455_, lean_object* v_idxPos_1456_, lean_object* v_recursorInfo_1457_, lean_object* v_idx_1458_, lean_object* v_tacticName_1459_, lean_object* v_mvarId_1460_, lean_object* v_majorType_1461_, lean_object* v_n_1462_, lean_object* v_i_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_zero_1469_; uint8_t v_isZero_1470_; 
v_zero_1469_ = lean_unsigned_to_nat(0u);
v_isZero_1470_ = lean_nat_dec_eq(v_i_1463_, v_zero_1469_);
if (v_isZero_1470_ == 1)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v_i_1463_);
lean_dec_ref(v_majorType_1461_);
lean_dec(v_mvarId_1460_);
lean_dec(v_tacticName_1459_);
lean_dec_ref(v_idx_1458_);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v_one_1473_; lean_object* v_n_1474_; lean_object* v___y_1476_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_arg_1480_; uint8_t v___x_1481_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v___x_1527_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v___x_1552_; 
v_one_1473_ = lean_unsigned_to_nat(1u);
v_n_1474_ = lean_nat_sub(v_i_1463_, v_one_1473_);
lean_dec(v_i_1463_);
v___x_1478_ = lean_nat_sub(v_n_1462_, v_n_1474_);
v___x_1479_ = lean_nat_sub(v___x_1478_, v_one_1473_);
lean_dec(v___x_1478_);
v_arg_1480_ = lean_array_fget_borrowed(v_majorTypeArgs_1455_, v___x_1479_);
v___x_1481_ = lean_nat_dec_lt(v_idxPos_1456_, v___x_1479_);
v___x_1527_ = lean_nat_dec_lt(v___x_1479_, v_idxPos_1456_);
v___x_1552_ = lean_nat_dec_eq(v___x_1479_, v_idxPos_1456_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_expr_eqv(v_arg_1480_, v_idx_1458_);
if (v___x_1553_ == 0)
{
v___y_1529_ = v___y_1464_;
v___y_1530_ = v___y_1465_;
v___y_1531_ = v___y_1466_;
v___y_1532_ = v___y_1467_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1554_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1458_);
v___x_1555_ = l_Lean_MessageData_ofExpr(v_idx_1458_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_inc_ref(v_majorType_1461_);
v___x_1559_ = l_Lean_indentExpr(v_majorType_1461_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_inc(v_mvarId_1460_);
lean_inc(v_tacticName_1459_);
v___x_1562_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1459_, v_mvarId_1460_, v___x_1561_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_dec_ref_known(v___x_1562_, 1);
v___y_1529_ = v___y_1464_;
v___y_1530_ = v___y_1465_;
v___y_1531_ = v___y_1466_;
v___y_1532_ = v___y_1467_;
goto v___jp_1528_;
}
else
{
lean_dec(v___x_1479_);
v___y_1476_ = v___x_1562_;
goto v___jp_1475_;
}
}
}
else
{
v___y_1529_ = v___y_1464_;
v___y_1530_ = v___y_1465_;
v___y_1531_ = v___y_1466_;
v___y_1532_ = v___y_1467_;
goto v___jp_1528_;
}
v___jp_1475_:
{
if (lean_obj_tag(v___y_1476_) == 0)
{
lean_dec_ref_known(v___y_1476_, 1);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_dec(v_n_1474_);
lean_dec_ref(v_majorType_1461_);
lean_dec(v_mvarId_1460_);
lean_dec(v_tacticName_1459_);
lean_dec_ref(v_idx_1458_);
return v___y_1476_;
}
}
v___jp_1482_:
{
if (v___x_1481_ == 0)
{
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_object* v_indicesPos_1488_; uint8_t v___x_1489_; 
v_indicesPos_1488_ = lean_ctor_get(v_recursorInfo_1457_, 6);
v___x_1489_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1479_, v_indicesPos_1488_);
if (v___x_1489_ == 0)
{
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
uint8_t v___x_1491_; 
v___x_1491_ = l_Lean_Expr_isFVar(v_arg_1480_);
if (v___x_1491_ == 0)
{
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = l_Lean_Expr_fvarId_x21(v_idx_1458_);
v___x_1494_ = l_Lean_FVarId_getDecl___redArg(v___x_1493_, v___y_1483_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1518_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1496_ = l_Lean_Expr_fvarId_x21(v_arg_1480_);
v___x_1497_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1495_, v___x_1496_, v___x_1489_, v___y_1484_);
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
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1504_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1458_);
v___x_1505_ = l_Lean_MessageData_ofExpr(v_idx_1458_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_nat_add(v___x_1479_, v_one_1473_);
lean_dec(v___x_1479_);
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
lean_inc(v_mvarId_1460_);
lean_inc(v_tacticName_1459_);
v___x_1516_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1459_, v_mvarId_1460_, v___x_1515_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
v___y_1476_ = v___x_1516_;
goto v___jp_1475_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v___x_1479_);
lean_dec(v_n_1474_);
lean_dec_ref(v_majorType_1461_);
lean_dec(v_mvarId_1460_);
lean_dec(v_tacticName_1459_);
lean_dec_ref(v_idx_1458_);
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
}
v___jp_1528_:
{
if (v___x_1527_ == 0)
{
v___y_1483_ = v___y_1529_;
v___y_1484_ = v___y_1530_;
v___y_1485_ = v___y_1531_;
v___y_1486_ = v___y_1532_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1551_; 
v___x_1533_ = l_Lean_Expr_fvarId_x21(v_idx_1458_);
lean_inc(v_arg_1480_);
v___x_1534_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1480_, v___x_1533_, v___y_1530_);
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
v___y_1483_ = v___y_1529_;
v___y_1484_ = v___y_1530_;
v___y_1485_ = v___y_1531_;
v___y_1486_ = v___y_1532_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1540_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1458_);
v___x_1541_ = l_Lean_MessageData_ofExpr(v_idx_1458_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
lean_inc_ref(v_majorType_1461_);
v___x_1545_ = l_Lean_indentExpr(v_majorType_1461_);
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
lean_inc(v_mvarId_1460_);
lean_inc(v_tacticName_1459_);
v___x_1549_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1459_, v_mvarId_1460_, v___x_1548_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_dec_ref_known(v___x_1549_, 1);
v___y_1483_ = v___y_1529_;
v___y_1484_ = v___y_1530_;
v___y_1485_ = v___y_1531_;
v___y_1486_ = v___y_1532_;
goto v___jp_1482_;
}
else
{
lean_dec(v___x_1479_);
v___y_1476_ = v___x_1549_;
goto v___jp_1475_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1563_, lean_object* v_idxPos_1564_, lean_object* v_recursorInfo_1565_, lean_object* v_idx_1566_, lean_object* v_tacticName_1567_, lean_object* v_mvarId_1568_, lean_object* v_majorType_1569_, lean_object* v_n_1570_, lean_object* v_i_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1563_, v_idxPos_1564_, v_recursorInfo_1565_, v_idx_1566_, v_tacticName_1567_, v_mvarId_1568_, v_majorType_1569_, v_n_1570_, v_i_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_n_1570_);
lean_dec_ref(v_recursorInfo_1565_);
lean_dec(v_idxPos_1564_);
lean_dec_ref(v_majorTypeArgs_1563_);
return v_res_1577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1587_, lean_object* v_recursorInfo_1588_, lean_object* v_tacticName_1589_, lean_object* v_mvarId_1590_, lean_object* v_majorType_1591_, size_t v_sz_1592_, size_t v_i_1593_, lean_object* v_bs_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_lt(v_i_1593_, v_sz_1592_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v_majorType_1591_);
lean_dec(v_mvarId_1590_);
lean_dec(v_tacticName_1589_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_bs_1594_);
return v___x_1601_;
}
else
{
lean_object* v_v_1602_; lean_object* v___x_1603_; lean_object* v_bs_x27_1604_; lean_object* v_a_1606_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v_v_1602_ = lean_array_uget(v_bs_1594_, v_i_1593_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v_bs_x27_1604_ = lean_array_uset(v_bs_1594_, v_i_1593_, v___x_1603_);
v___x_1611_ = lean_array_get_size(v_majorTypeArgs_1587_);
v___x_1612_ = lean_nat_dec_le(v___x_1611_, v_v_1602_);
if (v___x_1612_ == 0)
{
lean_object* v_idx_1613_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; uint8_t v___x_1628_; 
v_idx_1613_ = lean_array_fget_borrowed(v_majorTypeArgs_1587_, v_v_1602_);
v___x_1628_ = l_Lean_Expr_isFVar(v_idx_1613_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1613_);
v___x_1630_ = l_Lean_MessageData_ofExpr(v_idx_1613_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
lean_inc_ref(v_majorType_1591_);
v___x_1634_ = l_Lean_indentExpr(v_majorType_1591_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_inc(v_mvarId_1590_);
lean_inc(v_tacticName_1589_);
v___x_1637_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1589_, v_mvarId_1590_, v___x_1636_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_dec_ref_known(v___x_1637_, 1);
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_bs_x27_1604_);
lean_dec(v_v_1602_);
lean_dec_ref(v_majorType_1591_);
lean_dec(v_mvarId_1590_);
lean_dec(v_tacticName_1589_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
goto v___jp_1614_;
}
v___jp_1614_:
{
lean_object* v___x_1619_; 
lean_inc_ref(v_majorType_1591_);
lean_inc(v_mvarId_1590_);
lean_inc(v_tacticName_1589_);
lean_inc(v_idx_1613_);
v___x_1619_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1587_, v_v_1602_, v_recursorInfo_1588_, v_idx_1613_, v_tacticName_1589_, v_mvarId_1590_, v_majorType_1591_, v___x_1611_, v___x_1611_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v_v_1602_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_dec_ref_known(v___x_1619_, 1);
lean_inc(v_idx_1613_);
v_a_1606_ = v_idx_1613_;
goto v___jp_1605_;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_bs_x27_1604_);
lean_dec_ref(v_majorType_1591_);
lean_dec(v_mvarId_1590_);
lean_dec(v_tacticName_1589_);
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_v_1602_);
v___x_1646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1591_);
v___x_1647_ = l_Lean_indentExpr(v_majorType_1591_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_inc(v_mvarId_1590_);
lean_inc(v_tacticName_1589_);
v___x_1650_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1589_, v_mvarId_1590_, v___x_1649_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v_a_1606_ = v_a_1651_;
goto v___jp_1605_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_bs_x27_1604_);
lean_dec_ref(v_majorType_1591_);
lean_dec(v_mvarId_1590_);
lean_dec(v_tacticName_1589_);
v_a_1652_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1650_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
v___jp_1605_:
{
size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_add(v_i_1593_, v___x_1607_);
v___x_1609_ = lean_array_uset(v_bs_x27_1604_, v_i_1593_, v_a_1606_);
v_i_1593_ = v___x_1608_;
v_bs_1594_ = v___x_1609_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1660_, lean_object* v_recursorInfo_1661_, lean_object* v_tacticName_1662_, lean_object* v_mvarId_1663_, lean_object* v_majorType_1664_, lean_object* v_sz_1665_, lean_object* v_i_1666_, lean_object* v_bs_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
size_t v_sz_boxed_1673_; size_t v_i_boxed_1674_; lean_object* v_res_1675_; 
v_sz_boxed_1673_ = lean_unbox_usize(v_sz_1665_);
lean_dec(v_sz_1665_);
v_i_boxed_1674_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1660_, v_recursorInfo_1661_, v_tacticName_1662_, v_mvarId_1663_, v_majorType_1664_, v_sz_boxed_1673_, v_i_boxed_1674_, v_bs_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v_recursorInfo_1661_);
lean_dec_ref(v_majorTypeArgs_1660_);
return v_res_1675_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1676_; lean_object* v_dummy_1677_; 
v___x_1676_ = lean_box(0);
v_dummy_1677_ = l_Lean_Expr_sort___override(v___x_1676_);
return v_dummy_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1678_, lean_object* v_tacticName_1679_, lean_object* v_recursorInfo_1680_, lean_object* v_majorType_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_indicesPos_1687_; lean_object* v_nargs_1688_; lean_object* v_dummy_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_majorTypeArgs_1693_; lean_object* v___x_1694_; size_t v_sz_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v_indicesPos_1687_ = lean_ctor_get(v_recursorInfo_1680_, 6);
v_nargs_1688_ = l_Lean_Expr_getAppNumArgs(v_majorType_1681_);
v_dummy_1689_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1688_);
v___x_1690_ = lean_mk_array(v_nargs_1688_, v_dummy_1689_);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_sub(v_nargs_1688_, v___x_1691_);
lean_dec(v_nargs_1688_);
lean_inc_ref(v_majorType_1681_);
v_majorTypeArgs_1693_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1681_, v___x_1690_, v___x_1692_);
lean_inc(v_indicesPos_1687_);
v___x_1694_ = lean_array_mk(v_indicesPos_1687_);
v_sz_1695_ = lean_array_size(v___x_1694_);
v___x_1696_ = ((size_t)0ULL);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1693_, v_recursorInfo_1680_, v_tacticName_1679_, v_mvarId_1678_, v_majorType_1681_, v_sz_1695_, v___x_1696_, v___x_1694_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec_ref(v_recursorInfo_1680_);
lean_dec_ref(v_majorTypeArgs_1693_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1698_, lean_object* v_tacticName_1699_, lean_object* v_recursorInfo_1700_, lean_object* v_majorType_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1698_, v_tacticName_1699_, v_recursorInfo_1700_, v_majorType_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1708_, lean_object* v_idxPos_1709_, lean_object* v_recursorInfo_1710_, lean_object* v_idx_1711_, lean_object* v_tacticName_1712_, lean_object* v_mvarId_1713_, lean_object* v_majorType_1714_, lean_object* v_n_1715_, lean_object* v_i_1716_, lean_object* v_a_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1708_, v_idxPos_1709_, v_recursorInfo_1710_, v_idx_1711_, v_tacticName_1712_, v_mvarId_1713_, v_majorType_1714_, v_n_1715_, v_i_1716_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1724_, lean_object* v_idxPos_1725_, lean_object* v_recursorInfo_1726_, lean_object* v_idx_1727_, lean_object* v_tacticName_1728_, lean_object* v_mvarId_1729_, lean_object* v_majorType_1730_, lean_object* v_n_1731_, lean_object* v_i_1732_, lean_object* v_a_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1724_, v_idxPos_1725_, v_recursorInfo_1726_, v_idx_1727_, v_tacticName_1728_, v_mvarId_1729_, v_majorType_1730_, v_n_1731_, v_i_1732_, v_a_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_n_1731_);
lean_dec_ref(v_recursorInfo_1726_);
lean_dec(v_idxPos_1725_);
lean_dec_ref(v_majorTypeArgs_1724_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1740_, lean_object* v_msg_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_ref_1747_; lean_object* v_msg_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1758_; 
v_ref_1747_ = lean_ctor_get(v___y_1744_, 2);
v_msg_1748_ = l_Lean_MessageData_tagWithErrorName(v_msg_1741_, v_name_1740_);
v___x_1749_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1748_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1758_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1758_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_inc(v_ref_1747_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_ref_1747_);
lean_ctor_set(v___x_1754_, 1, v_a_1750_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 1);
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1756_ = v___x_1752_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1759_, lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1759_, v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1767_, lean_object* v___x_1768_, lean_object* v_tacticName_1769_, lean_object* v_mvarId_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
if (lean_obj_tag(v_x_1772_) == 0)
{
lean_object* v___x_1778_; 
lean_dec(v_mvarId_1770_);
lean_dec(v_tacticName_1769_);
lean_dec(v_a_1767_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_x_1771_);
return v___x_1778_;
}
else
{
lean_object* v_head_1779_; 
v_head_1779_ = lean_ctor_get(v_x_1772_, 0);
if (lean_obj_tag(v_head_1779_) == 0)
{
lean_object* v_tail_1780_; lean_object* v_fst_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1792_; 
v_tail_1780_ = lean_ctor_get(v_x_1772_, 1);
v_fst_1781_ = lean_ctor_get(v_x_1771_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_x_1771_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_x_1771_, 1);
lean_dec(v_unused_1793_);
v___x_1783_ = v_x_1771_;
v_isShared_1784_ = v_isSharedCheck_1792_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_fst_1781_);
lean_dec(v_x_1771_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1792_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_inc(v_a_1767_);
v___x_1785_ = lean_array_push(v_fst_1781_, v_a_1767_);
v___x_1786_ = 1;
v___x_1787_ = lean_box(v___x_1786_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 1, v___x_1787_);
lean_ctor_set(v___x_1783_, 0, v___x_1785_);
v___x_1789_ = v___x_1783_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v_x_1771_ = v___x_1789_;
v_x_1772_ = v_tail_1780_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1794_; lean_object* v_fst_1795_; lean_object* v_snd_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1813_; 
v_tail_1794_ = lean_ctor_get(v_x_1772_, 1);
v_fst_1795_ = lean_ctor_get(v_x_1771_, 0);
v_snd_1796_ = lean_ctor_get(v_x_1771_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1771_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1798_ = v_x_1771_;
v_isShared_1799_ = v_isSharedCheck_1813_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_snd_1796_);
lean_inc(v_fst_1795_);
lean_dec(v_x_1771_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1813_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_idx_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v_idx_1800_ = lean_ctor_get(v_head_1779_, 0);
v___x_1801_ = lean_array_get_size(v___x_1768_);
v___x_1802_ = lean_nat_dec_le(v___x_1801_, v_idx_1800_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = lean_array_fget_borrowed(v___x_1768_, v_idx_1800_);
lean_inc(v___x_1803_);
v___x_1804_ = lean_array_push(v_fst_1795_, v___x_1803_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1804_);
v___x_1806_ = v___x_1798_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_snd_1796_);
v___x_1806_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
v_x_1771_ = v___x_1806_;
v_x_1772_ = v_tail_1794_;
goto _start;
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1798_);
lean_dec(v_snd_1796_);
lean_dec(v_fst_1795_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1770_);
lean_inc(v_tacticName_1769_);
v___x_1810_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1769_, v_mvarId_1770_, v___x_1809_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v_x_1771_ = v_a_1811_;
v_x_1772_ = v_tail_1794_;
goto _start;
}
else
{
lean_dec(v_mvarId_1770_);
lean_dec(v_tacticName_1769_);
lean_dec(v_a_1767_);
return v___x_1810_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1814_, lean_object* v___x_1815_, lean_object* v_tacticName_1816_, lean_object* v_mvarId_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1814_, v___x_1815_, v_tacticName_1816_, v_mvarId_1817_, v_x_1818_, v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v_x_1819_);
lean_dec_ref(v___x_1815_);
return v_res_1825_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1850_ = l_Lean_MessageData_ofFormat(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1853_, lean_object* v_a_1854_, lean_object* v_tacticName_1855_, lean_object* v_mvarId_1856_, lean_object* v_indices_1857_, lean_object* v_a_1858_, lean_object* v_major_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 5)
{
lean_object* v_fn_1868_; lean_object* v_arg_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_fn_1868_ = lean_ctor_get(v_x_1860_, 0);
lean_inc_ref(v_fn_1868_);
v_arg_1869_ = lean_ctor_get(v_x_1860_, 1);
lean_inc_ref(v_arg_1869_);
lean_dec_ref_known(v_x_1860_, 2);
v___x_1870_ = lean_array_set(v_x_1861_, v_x_1862_, v_arg_1869_);
v___x_1871_ = lean_unsigned_to_nat(1u);
v___x_1872_ = lean_nat_sub(v_x_1862_, v___x_1871_);
lean_dec(v_x_1862_);
v_x_1860_ = v_fn_1868_;
v_x_1861_ = v___x_1870_;
v_x_1862_ = v___x_1872_;
goto _start;
}
else
{
lean_dec(v_x_1862_);
if (lean_obj_tag(v_x_1860_) == 4)
{
lean_object* v_us_1874_; lean_object* v_recursorName_1875_; lean_object* v_univLevelPos_1876_; uint8_t v_depElim_1877_; lean_object* v_paramsPos_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___y_1882_; lean_object* v_motive_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_us_1874_ = lean_ctor_get(v_x_1860_, 1);
lean_inc(v_us_1874_);
lean_dec_ref_known(v_x_1860_, 2);
v_recursorName_1875_ = lean_ctor_get(v_recursorInfo_1853_, 0);
lean_inc(v_recursorName_1875_);
v_univLevelPos_1876_ = lean_ctor_get(v_recursorInfo_1853_, 2);
lean_inc(v_univLevelPos_1876_);
v_depElim_1877_ = lean_ctor_get_uint8(v_recursorInfo_1853_, sizeof(void*)*8);
v_paramsPos_1878_ = lean_ctor_get(v_recursorInfo_1853_, 5);
lean_inc(v_paramsPos_1878_);
lean_dec_ref(v_recursorInfo_1853_);
v___x_1879_ = lean_array_mk(v_us_1874_);
v___x_1880_ = 0;
v___x_1900_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1856_);
lean_inc(v_tacticName_1855_);
lean_inc(v_a_1854_);
v___x_1901_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1854_, v___x_1879_, v_tacticName_1855_, v_mvarId_1856_, v___x_1900_, v_univLevelPos_1876_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v_univLevelPos_1876_);
lean_dec_ref(v___x_1879_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v_fst_1903_; lean_object* v_snd_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1948_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v_fst_1903_ = lean_ctor_get(v_a_1902_, 0);
v_snd_1904_ = lean_ctor_get(v_a_1902_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_a_1902_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1906_ = v_a_1902_;
v_isShared_1907_ = v_isSharedCheck_1948_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_snd_1904_);
lean_inc(v_fst_1903_);
lean_dec(v_a_1902_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1948_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___x_1928_; 
v___x_1928_ = lean_unbox(v_snd_1904_);
lean_dec(v_snd_1904_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = l_Lean_Level_isZero(v_a_1854_);
lean_dec(v_a_1854_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
lean_dec(v_fst_1903_);
lean_dec(v_paramsPos_1878_);
lean_dec_ref(v_x_1861_);
lean_dec_ref(v_major_1859_);
lean_dec_ref(v_a_1858_);
v___x_1930_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1931_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1932_ = l_Lean_MessageData_ofName(v_recursorName_1875_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 7);
lean_ctor_set(v___x_1906_, 1, v___x_1932_);
lean_ctor_set(v___x_1906_, 0, v___x_1931_);
v___x_1934_ = v___x_1906_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v___x_1935_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1855_, v_mvarId_1856_, v___x_1936_);
v___x_1938_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1930_, v___x_1937_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_del_object(v___x_1906_);
lean_dec(v_tacticName_1855_);
v___y_1909_ = v___y_1863_;
v___y_1910_ = v___y_1864_;
v___y_1911_ = v___y_1865_;
v___y_1912_ = v___y_1866_;
goto v___jp_1908_;
}
}
else
{
lean_del_object(v___x_1906_);
lean_dec(v_tacticName_1855_);
lean_dec(v_a_1854_);
v___y_1909_ = v___y_1863_;
v___y_1910_ = v___y_1864_;
v___y_1911_ = v___y_1865_;
v___y_1912_ = v___y_1866_;
goto v___jp_1908_;
}
v___jp_1908_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_array_to_list(v_fst_1903_);
v___x_1914_ = l_Lean_mkConst(v_recursorName_1875_, v___x_1913_);
v___x_1915_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1856_, v_x_1861_, v_paramsPos_1878_, v___x_1914_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec_ref(v_x_1861_);
if (lean_obj_tag(v___x_1915_) == 0)
{
if (v_depElim_1877_ == 0)
{
lean_object* v_a_1916_; 
lean_dec_ref(v_major_1859_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___y_1882_ = v_a_1916_;
v_motive_1883_ = v_a_1858_;
v___y_1884_ = v___y_1909_;
v___y_1885_ = v___y_1910_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1912_;
goto v___jp_1881_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1915_, 1);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc_ref(v_major_1859_);
v___x_1918_ = lean_infer_type(v_major_1859_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = lean_mk_empty_array_with_capacity(v___x_1920_);
v___x_1922_ = lean_array_push(v___x_1921_, v_major_1859_);
v___x_1923_ = l_Lean_Expr_abstractM(v_a_1858_, v___x_1922_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec_ref(v___x_1922_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1926_ = 0;
v___x_1927_ = l_Lean_mkLambda(v___x_1925_, v___x_1926_, v_a_1919_, v_a_1924_);
v___y_1882_ = v_a_1917_;
v_motive_1883_ = v___x_1927_;
v___y_1884_ = v___y_1909_;
v___y_1885_ = v___y_1910_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1912_;
goto v___jp_1881_;
}
else
{
lean_dec(v_a_1919_);
lean_dec(v_a_1917_);
return v___x_1923_;
}
}
else
{
lean_dec(v_a_1917_);
lean_dec_ref(v_major_1859_);
lean_dec_ref(v_a_1858_);
return v___x_1918_;
}
}
}
else
{
lean_dec_ref(v_major_1859_);
lean_dec_ref(v_a_1858_);
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_paramsPos_1878_);
lean_dec(v_recursorName_1875_);
lean_dec_ref(v_x_1861_);
lean_dec_ref(v_major_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_mvarId_1856_);
lean_dec(v_tacticName_1855_);
lean_dec(v_a_1854_);
v_a_1949_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1901_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1901_);
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
v___jp_1881_:
{
uint8_t v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = 1;
v___x_1889_ = 1;
v___x_1890_ = l_Lean_Meta_mkLambdaFVars(v_indices_1857_, v_motive_1883_, v___x_1880_, v___x_1888_, v___x_1880_, v___x_1888_, v___x_1889_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = l_Lean_Expr_app___override(v___y_1882_, v_a_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_dec_ref(v___y_1882_);
return v___x_1890_;
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec_ref(v_x_1861_);
lean_dec_ref(v_x_1860_);
lean_dec_ref(v_major_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1854_);
lean_dec_ref(v_recursorInfo_1853_);
v___x_1957_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1958_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1855_, v_mvarId_1856_, v___x_1957_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1959_, lean_object* v_a_1960_, lean_object* v_tacticName_1961_, lean_object* v_mvarId_1962_, lean_object* v_indices_1963_, lean_object* v_a_1964_, lean_object* v_major_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1959_, v_a_1960_, v_tacticName_1961_, v_mvarId_1962_, v_indices_1963_, v_a_1964_, v_major_1965_, v_x_1966_, v_x_1967_, v_x_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec_ref(v_indices_1963_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1975_, lean_object* v_tacticName_1976_, lean_object* v_mvarId_1977_, lean_object* v_recursorInfo_1978_, lean_object* v_indices_1979_, lean_object* v_a_1980_, lean_object* v_major_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 5)
{
lean_object* v_fn_1990_; lean_object* v_arg_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_fn_1990_ = lean_ctor_get(v_x_1982_, 0);
lean_inc_ref(v_fn_1990_);
v_arg_1991_ = lean_ctor_get(v_x_1982_, 1);
lean_inc_ref(v_arg_1991_);
lean_dec_ref_known(v_x_1982_, 2);
v___x_1992_ = lean_array_set(v_x_1983_, v_x_1984_, v_arg_1991_);
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_nat_sub(v_x_1984_, v___x_1993_);
v___x_1995_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1978_, v_a_1975_, v_tacticName_1976_, v_mvarId_1977_, v_indices_1979_, v_a_1980_, v_major_1981_, v_fn_1990_, v___x_1992_, v___x_1994_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1995_;
}
else
{
if (lean_obj_tag(v_x_1982_) == 4)
{
lean_object* v_us_1996_; lean_object* v_recursorName_1997_; lean_object* v_univLevelPos_1998_; uint8_t v_depElim_1999_; lean_object* v_paramsPos_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___y_2004_; lean_object* v_motive_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_us_1996_ = lean_ctor_get(v_x_1982_, 1);
lean_inc(v_us_1996_);
lean_dec_ref_known(v_x_1982_, 2);
v_recursorName_1997_ = lean_ctor_get(v_recursorInfo_1978_, 0);
lean_inc(v_recursorName_1997_);
v_univLevelPos_1998_ = lean_ctor_get(v_recursorInfo_1978_, 2);
lean_inc(v_univLevelPos_1998_);
v_depElim_1999_ = lean_ctor_get_uint8(v_recursorInfo_1978_, sizeof(void*)*8);
v_paramsPos_2000_ = lean_ctor_get(v_recursorInfo_1978_, 5);
lean_inc(v_paramsPos_2000_);
lean_dec_ref(v_recursorInfo_1978_);
v___x_2001_ = lean_array_mk(v_us_1996_);
v___x_2002_ = 0;
v___x_2022_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1977_);
lean_inc(v_tacticName_1976_);
lean_inc(v_a_1975_);
v___x_2023_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1975_, v___x_2001_, v_tacticName_1976_, v_mvarId_1977_, v___x_2022_, v_univLevelPos_1998_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v_univLevelPos_1998_);
lean_dec_ref(v___x_2001_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2070_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v_fst_2025_ = lean_ctor_get(v_a_2024_, 0);
v_snd_2026_ = lean_ctor_get(v_a_2024_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2028_ = v_a_2024_;
v_isShared_2029_ = v_isSharedCheck_2070_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_inc(v_fst_2025_);
lean_dec(v_a_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2070_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; uint8_t v___x_2050_; 
v___x_2050_ = lean_unbox(v_snd_2026_);
lean_dec(v_snd_2026_);
if (v___x_2050_ == 0)
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_Level_isZero(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_dec(v_fst_2025_);
lean_dec(v_paramsPos_2000_);
lean_dec_ref(v_x_1983_);
lean_dec_ref(v_major_1981_);
lean_dec_ref(v_a_1980_);
v___x_2052_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2053_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2054_ = l_Lean_MessageData_ofName(v_recursorName_1997_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 7);
lean_ctor_set(v___x_2028_, 1, v___x_2054_);
lean_ctor_set(v___x_2028_, 0, v___x_2053_);
v___x_2056_ = v___x_2028_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v___x_2057_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1976_, v_mvarId_1977_, v___x_2058_);
v___x_2060_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2052_, v___x_2059_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_del_object(v___x_2028_);
lean_dec(v_tacticName_1976_);
v___y_2031_ = v___y_1985_;
v___y_2032_ = v___y_1986_;
v___y_2033_ = v___y_1987_;
v___y_2034_ = v___y_1988_;
goto v___jp_2030_;
}
}
else
{
lean_del_object(v___x_2028_);
lean_dec(v_tacticName_1976_);
lean_dec(v_a_1975_);
v___y_2031_ = v___y_1985_;
v___y_2032_ = v___y_1986_;
v___y_2033_ = v___y_1987_;
v___y_2034_ = v___y_1988_;
goto v___jp_2030_;
}
v___jp_2030_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_array_to_list(v_fst_2025_);
v___x_2036_ = l_Lean_mkConst(v_recursorName_1997_, v___x_2035_);
v___x_2037_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1977_, v_x_1983_, v_paramsPos_2000_, v___x_2036_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec_ref(v_x_1983_);
if (lean_obj_tag(v___x_2037_) == 0)
{
if (v_depElim_1999_ == 0)
{
lean_object* v_a_2038_; 
lean_dec_ref(v_major_1981_);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___y_2004_ = v_a_2038_;
v_motive_2005_ = v_a_1980_;
v___y_2006_ = v___y_2031_;
v___y_2007_ = v___y_2032_;
v___y_2008_ = v___y_2033_;
v___y_2009_ = v___y_2034_;
goto v___jp_2003_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2037_, 1);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
lean_inc_ref(v_major_1981_);
v___x_2040_ = lean_infer_type(v_major_1981_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = lean_mk_empty_array_with_capacity(v___x_2042_);
v___x_2044_ = lean_array_push(v___x_2043_, v_major_1981_);
v___x_2045_ = l_Lean_Expr_abstractM(v_a_1980_, v___x_2044_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec_ref(v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2048_ = 0;
v___x_2049_ = l_Lean_mkLambda(v___x_2047_, v___x_2048_, v_a_2041_, v_a_2046_);
v___y_2004_ = v_a_2039_;
v_motive_2005_ = v___x_2049_;
v___y_2006_ = v___y_2031_;
v___y_2007_ = v___y_2032_;
v___y_2008_ = v___y_2033_;
v___y_2009_ = v___y_2034_;
goto v___jp_2003_;
}
else
{
lean_dec(v_a_2041_);
lean_dec(v_a_2039_);
return v___x_2045_;
}
}
else
{
lean_dec(v_a_2039_);
lean_dec_ref(v_major_1981_);
lean_dec_ref(v_a_1980_);
return v___x_2040_;
}
}
}
else
{
lean_dec_ref(v_major_1981_);
lean_dec_ref(v_a_1980_);
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_paramsPos_2000_);
lean_dec(v_recursorName_1997_);
lean_dec_ref(v_x_1983_);
lean_dec_ref(v_major_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_mvarId_1977_);
lean_dec(v_tacticName_1976_);
lean_dec(v_a_1975_);
v_a_2071_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2023_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2023_);
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
v___jp_2003_:
{
uint8_t v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = 1;
v___x_2011_ = 1;
v___x_2012_ = l_Lean_Meta_mkLambdaFVars(v_indices_1979_, v_motive_2005_, v___x_2002_, v___x_2010_, v___x_2002_, v___x_2010_, v___x_2011_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2021_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = l_Lean_Expr_app___override(v___y_2004_, v_a_2013_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2017_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
else
{
lean_dec_ref(v___y_2004_);
return v___x_2012_;
}
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref(v_x_1983_);
lean_dec_ref(v_x_1982_);
lean_dec_ref(v_major_1981_);
lean_dec_ref(v_a_1980_);
lean_dec_ref(v_recursorInfo_1978_);
lean_dec(v_a_1975_);
v___x_2079_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2080_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1976_, v_mvarId_1977_, v___x_2079_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2081_, lean_object* v_tacticName_2082_, lean_object* v_mvarId_2083_, lean_object* v_recursorInfo_2084_, lean_object* v_indices_2085_, lean_object* v_a_2086_, lean_object* v_major_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2081_, v_tacticName_2082_, v_mvarId_2083_, v_recursorInfo_2084_, v_indices_2085_, v_a_2086_, v_major_2087_, v_x_2088_, v_x_2089_, v_x_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v_x_2090_);
lean_dec_ref(v_indices_2085_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2097_, lean_object* v_tacticName_2098_, lean_object* v_majorFVarId_2099_, lean_object* v_recursorInfo_2100_, lean_object* v_indices_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; 
lean_inc(v_mvarId_2097_);
v___x_2107_ = l_Lean_MVarId_getType(v_mvarId_2097_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc_n(v_a_2108_, 2);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Meta_getLevel(v_a_2108_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = l_Lean_Meta_normalizeLevel(v_a_2110_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v_major_2113_; lean_object* v___x_2114_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
lean_inc(v_majorFVarId_2099_);
v_major_2113_ = l_Lean_mkFVar(v_majorFVarId_2099_);
v___x_2114_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2099_, v_a_2102_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_typeName_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v_typeName_2116_ = lean_ctor_get(v_recursorInfo_2100_, 1);
v___x_2117_ = l_Lean_LocalDecl_type(v_a_2115_);
lean_dec(v_a_2115_);
lean_inc_ref(v___x_2117_);
v___x_2118_ = l_Lean_Meta_whnfUntil(v___x_2117_, v_typeName_2116_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
if (lean_obj_tag(v_a_2119_) == 1)
{
lean_object* v_val_2120_; lean_object* v_dummy_2121_; lean_object* v_nargs_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v___x_2117_);
v_val_2120_ = lean_ctor_get(v_a_2119_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_a_2119_, 1);
v_dummy_2121_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2122_ = l_Lean_Expr_getAppNumArgs(v_val_2120_);
lean_inc(v_nargs_2122_);
v___x_2123_ = lean_mk_array(v_nargs_2122_, v_dummy_2121_);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_sub(v_nargs_2122_, v___x_2124_);
lean_dec(v_nargs_2122_);
v___x_2126_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2112_, v_tacticName_2098_, v_mvarId_2097_, v_recursorInfo_2100_, v_indices_2101_, v_a_2108_, v_major_2113_, v_val_2120_, v___x_2123_, v___x_2125_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v___x_2125_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; 
lean_dec(v_a_2119_);
lean_dec_ref(v_major_2113_);
lean_dec(v_a_2112_);
lean_dec(v_a_2108_);
lean_dec_ref(v_recursorInfo_2100_);
v___x_2127_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2098_, v_mvarId_2097_, v___x_2117_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
return v___x_2127_;
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_major_2113_);
lean_dec(v_a_2112_);
lean_dec(v_a_2108_);
lean_dec_ref(v_recursorInfo_2100_);
lean_dec(v_tacticName_2098_);
lean_dec(v_mvarId_2097_);
v_a_2128_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2118_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2118_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_major_2113_);
lean_dec(v_a_2112_);
lean_dec(v_a_2108_);
lean_dec_ref(v_recursorInfo_2100_);
lean_dec(v_tacticName_2098_);
lean_dec(v_mvarId_2097_);
v_a_2136_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2114_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2114_);
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
lean_dec(v_a_2108_);
lean_dec_ref(v_recursorInfo_2100_);
lean_dec(v_majorFVarId_2099_);
lean_dec(v_tacticName_2098_);
lean_dec(v_mvarId_2097_);
v_a_2144_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2111_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2111_);
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
lean_dec(v_a_2108_);
lean_dec_ref(v_recursorInfo_2100_);
lean_dec(v_majorFVarId_2099_);
lean_dec(v_tacticName_2098_);
lean_dec(v_mvarId_2097_);
v_a_2152_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2109_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2109_);
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
lean_dec_ref(v_recursorInfo_2100_);
lean_dec(v_majorFVarId_2099_);
lean_dec(v_tacticName_2098_);
lean_dec(v_mvarId_2097_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2160_, lean_object* v_tacticName_2161_, lean_object* v_majorFVarId_2162_, lean_object* v_recursorInfo_2163_, lean_object* v_indices_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2160_, v_tacticName_2161_, v_majorFVarId_2162_, v_recursorInfo_2163_, v_indices_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_indices_2164_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2171_, lean_object* v_name_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2172_, v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_name_2181_, lean_object* v_msg_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2180_, v_name_2181_, v_msg_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2189_, v_x_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_a_2205_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2196_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2196_);
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
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2213_, v_x_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2221_, lean_object* v_mvarId_2222_, lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2222_, v_x_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2230_, lean_object* v_mvarId_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2230_, v_mvarId_2231_, v_x_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2239_, lean_object* v_as_2240_, size_t v_sz_2241_, size_t v_i_2242_, lean_object* v_b_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_usize_dec_lt(v_i_2242_, v_sz_2241_);
if (v___x_2244_ == 0)
{
return v_b_2243_;
}
else
{
lean_object* v_fst_2245_; lean_object* v_snd_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2264_; 
v_fst_2245_ = lean_ctor_get(v_b_2243_, 0);
v_snd_2246_ = lean_ctor_get(v_b_2243_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_b_2243_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2248_ = v_b_2243_;
v_isShared_2249_ = v_isSharedCheck_2264_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snd_2246_);
lean_inc(v_fst_2245_);
lean_dec(v_b_2243_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2264_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v_a_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2250_ = lean_box(0);
v_a_2251_ = lean_array_uget_borrowed(v_as_2240_, v_i_2242_);
v___x_2252_ = l_Lean_Expr_fvarId_x21(v_a_2251_);
v___x_2253_ = lean_array_get_borrowed(v___x_2250_, v_fst_2239_, v_snd_2246_);
lean_inc(v___x_2253_);
v___x_2254_ = l_Lean_mkFVar(v___x_2253_);
v___x_2255_ = l_Lean_Meta_FVarSubst_insert(v_fst_2245_, v___x_2252_, v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_add(v_snd_2246_, v___x_2256_);
lean_dec(v_snd_2246_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2257_);
lean_ctor_set(v___x_2248_, 0, v___x_2255_);
v___x_2259_ = v___x_2248_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
size_t v___x_2260_; size_t v___x_2261_; 
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2242_, v___x_2260_);
v_i_2242_ = v___x_2261_;
v_b_2243_ = v___x_2259_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2265_, lean_object* v_as_2266_, lean_object* v_sz_2267_, lean_object* v_i_2268_, lean_object* v_b_2269_){
_start:
{
size_t v_sz_boxed_2270_; size_t v_i_boxed_2271_; lean_object* v_res_2272_; 
v_sz_boxed_2270_ = lean_unbox_usize(v_sz_2267_);
lean_dec(v_sz_2267_);
v_i_boxed_2271_ = lean_unbox_usize(v_i_2268_);
lean_dec(v_i_2268_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2265_, v_as_2266_, v_sz_boxed_2270_, v_i_boxed_2271_, v_b_2269_);
lean_dec_ref(v_as_2266_);
lean_dec_ref(v_fst_2265_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2273_, lean_object* v___x_2274_, lean_object* v_fst_2275_, lean_object* v_a_2276_, lean_object* v___x_2277_, lean_object* v_givenNames_2278_, lean_object* v_fst_2279_, lean_object* v___x_2280_, lean_object* v_fst_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
lean_inc_ref(v_a_2276_);
lean_inc(v_snd_2273_);
v___x_2287_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2273_, v___x_2274_, v_fst_2275_, v_a_2276_, v___x_2277_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2273_, v_givenNames_2278_, v_a_2276_, v_fst_2279_, v___x_2280_, v___x_2277_, v_fst_2281_, v_a_2288_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec_ref(v_a_2276_);
return v___x_2289_;
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_fst_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v_a_2276_);
lean_dec(v_snd_2273_);
v_a_2290_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2287_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2287_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2298_, lean_object* v___x_2299_, lean_object* v_fst_2300_, lean_object* v_a_2301_, lean_object* v___x_2302_, lean_object* v_givenNames_2303_, lean_object* v_fst_2304_, lean_object* v___x_2305_, lean_object* v_fst_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2298_, v___x_2299_, v_fst_2300_, v_a_2301_, v___x_2302_, v_givenNames_2303_, v_fst_2304_, v___x_2305_, v_fst_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_fst_2304_);
lean_dec_ref(v_givenNames_2303_);
lean_dec_ref(v___x_2302_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_bs_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2316_ == 0)
{
return v_bs_2315_;
}
else
{
lean_object* v_v_2317_; lean_object* v___x_2318_; lean_object* v_bs_x27_2319_; lean_object* v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v_v_2317_ = lean_array_uget(v_bs_2315_, v_i_2314_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v_bs_x27_2319_ = lean_array_uset(v_bs_2315_, v_i_2314_, v___x_2318_);
v___x_2320_ = l_Lean_Expr_fvarId_x21(v_v_2317_);
lean_dec(v_v_2317_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2314_, v___x_2321_);
v___x_2323_ = lean_array_uset(v_bs_x27_2319_, v_i_2314_, v___x_2320_);
v_i_2314_ = v___x_2322_;
v_bs_2315_ = v___x_2323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2325_, lean_object* v_i_2326_, lean_object* v_bs_2327_){
_start:
{
size_t v_sz_boxed_2328_; size_t v_i_boxed_2329_; lean_object* v_res_2330_; 
v_sz_boxed_2328_ = lean_unbox_usize(v_sz_2325_);
lean_dec(v_sz_2325_);
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_res_2330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2328_, v_i_boxed_2329_, v_bs_2327_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2331_, lean_object* v_val_2332_, lean_object* v_mvarId_2333_, lean_object* v_as_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
if (lean_obj_tag(v_as_2334_) == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_mvarId_2333_);
lean_dec_ref(v_val_2332_);
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
else
{
lean_object* v_head_2342_; 
v_head_2342_ = lean_ctor_get(v_as_2334_, 0);
lean_inc(v_head_2342_);
if (lean_obj_tag(v_head_2342_) == 0)
{
lean_object* v_tail_2343_; 
v_tail_2343_ = lean_ctor_get(v_as_2334_, 1);
lean_inc(v_tail_2343_);
lean_dec_ref_known(v_as_2334_, 2);
v_as_2334_ = v_tail_2343_;
goto _start;
}
else
{
lean_object* v_tail_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2368_; 
v_tail_2345_ = lean_ctor_get(v_as_2334_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_as_2334_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v_as_2334_, 0);
lean_dec(v_unused_2369_);
v___x_2347_ = v_as_2334_;
v_isShared_2348_ = v_isSharedCheck_2368_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_tail_2345_);
lean_dec(v_as_2334_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2368_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v_val_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2367_; 
v_val_2349_ = lean_ctor_get(v_head_2342_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_head_2342_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2351_ = v_head_2342_;
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_val_2349_);
lean_dec(v_head_2342_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = lean_array_get_size(v_majorTypeArgs_2331_);
v___x_2354_ = lean_nat_dec_le(v___x_2353_, v_val_2349_);
lean_dec(v_val_2349_);
if (v___x_2354_ == 0)
{
lean_del_object(v___x_2351_);
lean_del_object(v___x_2347_);
v_as_2334_ = v_tail_2345_;
goto _start;
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2357_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2332_);
v___x_2358_ = l_Lean_indentExpr(v_val_2332_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 7);
lean_ctor_set(v___x_2347_, 1, v___x_2358_);
lean_ctor_set(v___x_2347_, 0, v___x_2357_);
v___x_2360_ = v___x_2347_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2360_);
v___x_2362_ = v___x_2351_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; 
lean_inc(v_mvarId_2333_);
v___x_2363_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2356_, v_mvarId_2333_, v___x_2362_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref_known(v___x_2363_, 1);
v_as_2334_ = v_tail_2345_;
goto _start;
}
else
{
lean_dec(v_tail_2345_);
lean_dec(v_mvarId_2333_);
lean_dec_ref(v_val_2332_);
return v___x_2363_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2370_, lean_object* v_val_2371_, lean_object* v_mvarId_2372_, lean_object* v_as_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2370_, v_val_2371_, v_mvarId_2372_, v_as_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v_majorTypeArgs_2370_);
return v_res_2379_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2389_, lean_object* v_val_2390_, lean_object* v_mvarId_2391_, lean_object* v_majorFVarId_2392_, lean_object* v_givenNames_2393_, lean_object* v_recursorName_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
if (lean_obj_tag(v_x_2395_) == 5)
{
lean_object* v_fn_2403_; lean_object* v_arg_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_fn_2403_ = lean_ctor_get(v_x_2395_, 0);
lean_inc_ref(v_fn_2403_);
v_arg_2404_ = lean_ctor_get(v_x_2395_, 1);
lean_inc_ref(v_arg_2404_);
lean_dec_ref_known(v_x_2395_, 2);
v___x_2405_ = lean_array_set(v_x_2396_, v_x_2397_, v_arg_2404_);
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_sub(v_x_2397_, v___x_2406_);
lean_dec(v_x_2397_);
v_x_2395_ = v_fn_2403_;
v_x_2396_ = v___x_2405_;
v_x_2397_ = v___x_2407_;
goto _start;
}
else
{
uint8_t v_depElim_2409_; lean_object* v_paramsPos_2410_; lean_object* v___x_2411_; 
lean_dec(v_x_2397_);
lean_dec_ref(v_x_2395_);
v_depElim_2409_ = lean_ctor_get_uint8(v_a_2389_, sizeof(void*)*8);
v_paramsPos_2410_ = lean_ctor_get(v_a_2389_, 5);
lean_inc(v_paramsPos_2410_);
lean_inc(v_mvarId_2391_);
lean_inc_ref(v_val_2390_);
v___x_2411_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2396_, v_val_2390_, v_mvarId_2391_, v_paramsPos_2410_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec_ref(v_x_2396_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; size_t v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___x_2430_; 
lean_dec_ref_known(v___x_2411_, 1);
v___x_2412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2389_);
lean_inc(v_mvarId_2391_);
v___x_2430_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2391_, v___x_2412_, v_a_2389_, v_val_2390_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
lean_inc(v_mvarId_2391_);
v___x_2432_ = l_Lean_MVarId_getType(v_mvarId_2391_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_cls_2434_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v_cls_2434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2409_ == 0)
{
lean_object* v___x_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2546_; 
lean_inc(v_majorFVarId_2392_);
v___x_2523_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2433_, v_majorFVarId_2392_, v___y_2399_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2546_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2546_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_unbox(v_a_2524_);
lean_dec(v_a_2524_);
if (v___x_2528_ == 0)
{
lean_del_object(v___x_2526_);
lean_dec(v_recursorName_2394_);
v___y_2436_ = v___y_2398_;
v___y_2437_ = v___y_2399_;
v___y_2438_ = v___y_2400_;
v___y_2439_ = v___y_2401_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2529_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2530_ = l_Lean_MessageData_ofName(v_recursorName_2394_);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2533_);
v___x_2535_ = v___x_2526_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; 
lean_inc(v_mvarId_2391_);
v___x_2536_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2412_, v_mvarId_2391_, v___x_2535_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_dec_ref_known(v___x_2536_, 1);
v___y_2436_ = v___y_2398_;
v___y_2437_ = v___y_2399_;
v___y_2438_ = v___y_2400_;
v___y_2439_ = v___y_2401_;
goto v___jp_2435_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2431_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec(v_mvarId_2391_);
lean_dec_ref(v_a_2389_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2433_);
lean_dec(v_recursorName_2394_);
v___y_2436_ = v___y_2398_;
v___y_2437_ = v___y_2399_;
v___y_2438_ = v___y_2400_;
v___y_2439_ = v___y_2401_;
goto v___jp_2435_;
}
v___jp_2435_:
{
size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; 
v_sz_2440_ = lean_array_size(v_a_2431_);
v___x_2441_ = ((size_t)0ULL);
lean_inc(v_a_2431_);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2440_, v___x_2441_, v_a_2431_);
lean_inc(v_majorFVarId_2392_);
v___x_2443_ = lean_array_push(v___x_2442_, v_majorFVarId_2392_);
v___x_2444_ = 1;
v___x_2445_ = 0;
v___x_2446_ = l_Lean_MVarId_revert(v_mvarId_2391_, v___x_2443_, v___x_2444_, v___x_2445_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v_fst_2448_; lean_object* v_snd_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v_fst_2448_ = lean_ctor_get(v_a_2447_, 0);
lean_inc(v_fst_2448_);
v_snd_2449_ = lean_ctor_get(v_a_2447_, 1);
lean_inc(v_snd_2449_);
lean_dec(v_a_2447_);
v___x_2450_ = lean_array_get_size(v_a_2431_);
v___x_2451_ = lean_box(0);
v___x_2452_ = l_Lean_Meta_introNCore(v_snd_2449_, v___x_2450_, v___x_2451_, v___x_2445_, v___x_2444_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v_fst_2454_; lean_object* v_snd_2455_; lean_object* v___x_2456_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v_fst_2454_ = lean_ctor_get(v_a_2453_, 0);
lean_inc(v_fst_2454_);
v_snd_2455_ = lean_ctor_get(v_a_2453_, 1);
lean_inc(v_snd_2455_);
lean_dec(v_a_2453_);
v___x_2456_ = l_Lean_Meta_intro1Core(v_snd_2455_, v___x_2444_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v_fst_2458_; lean_object* v_snd_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2498_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v_fst_2458_ = lean_ctor_get(v_a_2457_, 0);
v_snd_2459_ = lean_ctor_get(v_a_2457_, 1);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2461_ = v_a_2457_;
v_isShared_2462_ = v_isSharedCheck_2498_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_snd_2459_);
lean_inc(v_fst_2458_);
lean_dec(v_a_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2498_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2463_ = lean_box(0);
lean_inc(v_fst_2458_);
v___x_2464_ = l_Lean_mkFVar(v_fst_2458_);
lean_inc_ref(v___x_2464_);
v___x_2465_ = l_Lean_Meta_FVarSubst_insert(v___x_2463_, v_majorFVarId_2392_, v___x_2464_);
v___x_2466_ = lean_unsigned_to_nat(0u);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v___x_2466_);
lean_ctor_set(v___x_2461_, 0, v___x_2465_);
v___x_2468_ = v___x_2461_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; lean_object* v_toCold_2470_; lean_object* v_options_2471_; uint8_t v_hasTrace_2472_; 
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2454_, v_a_2431_, v_sz_2440_, v___x_2441_, v___x_2468_);
lean_dec(v_a_2431_);
v_toCold_2470_ = lean_ctor_get(v___y_2438_, 0);
v_options_2471_ = lean_ctor_get(v_toCold_2470_, 2);
v_hasTrace_2472_ = lean_ctor_get_uint8(v_options_2471_, sizeof(void*)*1);
if (v_hasTrace_2472_ == 0)
{
lean_object* v_fst_2473_; 
v_fst_2473_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_fst_2473_);
lean_dec_ref(v___x_2469_);
lean_inc(v_snd_2459_);
v___y_2414_ = v___x_2464_;
v___y_2415_ = v_fst_2458_;
v___y_2416_ = v_fst_2473_;
v___y_2417_ = v_fst_2448_;
v___y_2418_ = v_snd_2459_;
v___y_2419_ = v___x_2441_;
v___y_2420_ = v_fst_2454_;
v___y_2421_ = v_snd_2459_;
v___y_2422_ = v___y_2436_;
v___y_2423_ = v___y_2437_;
v___y_2424_ = v___y_2438_;
v___y_2425_ = v___y_2439_;
goto v___jp_2413_;
}
else
{
lean_object* v_fst_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2495_; 
v_fst_2474_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2469_, 1);
lean_dec(v_unused_2496_);
v___x_2476_ = v___x_2469_;
v_isShared_2477_ = v_isSharedCheck_2495_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_fst_2474_);
lean_dec(v___x_2469_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2495_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_inheritedTraceOptions_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_inheritedTraceOptions_2478_ = lean_ctor_get(v_toCold_2470_, 11);
v___x_2479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2478_, v_options_2471_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_del_object(v___x_2476_);
lean_inc(v_snd_2459_);
v___y_2414_ = v___x_2464_;
v___y_2415_ = v_fst_2458_;
v___y_2416_ = v_fst_2474_;
v___y_2417_ = v_fst_2448_;
v___y_2418_ = v_snd_2459_;
v___y_2419_ = v___x_2441_;
v___y_2420_ = v_fst_2454_;
v___y_2421_ = v_snd_2459_;
v___y_2422_ = v___y_2436_;
v___y_2423_ = v___y_2437_;
v___y_2424_ = v___y_2438_;
v___y_2425_ = v___y_2439_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2481_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2459_);
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_snd_2459_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set_tag(v___x_2476_, 7);
lean_ctor_set(v___x_2476_, 1, v___x_2482_);
lean_ctor_set(v___x_2476_, 0, v___x_2481_);
v___x_2484_ = v___x_2476_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2434_, v___x_2484_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_dec_ref_known(v___x_2485_, 1);
lean_inc(v_snd_2459_);
v___y_2414_ = v___x_2464_;
v___y_2415_ = v_fst_2458_;
v___y_2416_ = v_fst_2474_;
v___y_2417_ = v_fst_2448_;
v___y_2418_ = v_snd_2459_;
v___y_2419_ = v___x_2441_;
v___y_2420_ = v_fst_2454_;
v___y_2421_ = v_snd_2459_;
v___y_2422_ = v___y_2436_;
v___y_2423_ = v___y_2437_;
v___y_2424_ = v___y_2438_;
v___y_2425_ = v___y_2439_;
goto v___jp_2413_;
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_fst_2474_);
lean_dec_ref(v___x_2464_);
lean_dec(v_snd_2459_);
lean_dec(v_fst_2458_);
lean_dec(v_fst_2454_);
lean_dec(v_fst_2448_);
lean_dec_ref(v_givenNames_2393_);
lean_dec_ref(v_a_2389_);
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
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
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_fst_2454_);
lean_dec(v_fst_2448_);
lean_dec(v_a_2431_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec_ref(v_a_2389_);
v_a_2499_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2456_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2456_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_fst_2448_);
lean_dec(v_a_2431_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec_ref(v_a_2389_);
v_a_2507_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2452_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2452_);
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
lean_dec(v_a_2431_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec_ref(v_a_2389_);
v_a_2515_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2446_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2446_);
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
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_a_2431_);
lean_dec(v_recursorName_2394_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec(v_mvarId_2391_);
lean_dec_ref(v_a_2389_);
v_a_2547_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2432_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2432_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_recursorName_2394_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec(v_mvarId_2391_);
lean_dec_ref(v_a_2389_);
v_a_2555_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2430_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2430_);
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
v___jp_2413_:
{
size_t v_sz_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; 
v_sz_2426_ = lean_array_size(v___y_2420_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2426_, v___y_2419_, v___y_2420_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2428_, 0, v___y_2418_);
lean_closure_set(v___f_2428_, 1, v___x_2412_);
lean_closure_set(v___f_2428_, 2, v___y_2415_);
lean_closure_set(v___f_2428_, 3, v_a_2389_);
lean_closure_set(v___f_2428_, 4, v___x_2427_);
lean_closure_set(v___f_2428_, 5, v_givenNames_2393_);
lean_closure_set(v___f_2428_, 6, v___y_2417_);
lean_closure_set(v___f_2428_, 7, v___y_2414_);
lean_closure_set(v___f_2428_, 8, v___y_2416_);
v___x_2429_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2421_, v___f_2428_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2429_;
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_recursorName_2394_);
lean_dec_ref(v_givenNames_2393_);
lean_dec(v_majorFVarId_2392_);
lean_dec(v_mvarId_2391_);
lean_dec_ref(v_val_2390_);
lean_dec_ref(v_a_2389_);
v_a_2563_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2411_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2411_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2571_, lean_object* v_val_2572_, lean_object* v_mvarId_2573_, lean_object* v_majorFVarId_2574_, lean_object* v_givenNames_2575_, lean_object* v_recursorName_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2571_, v_val_2572_, v_mvarId_2573_, v_majorFVarId_2574_, v_givenNames_2575_, v_recursorName_2576_, v_x_2577_, v_x_2578_, v_x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2586_, lean_object* v_mvarId_2587_, lean_object* v_a_2588_, lean_object* v_majorFVarId_2589_, lean_object* v_givenNames_2590_, lean_object* v_recursorName_2591_, lean_object* v_x_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
if (lean_obj_tag(v_x_2592_) == 5)
{
lean_object* v_fn_2600_; lean_object* v_arg_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_fn_2600_ = lean_ctor_get(v_x_2592_, 0);
lean_inc_ref(v_fn_2600_);
v_arg_2601_ = lean_ctor_get(v_x_2592_, 1);
lean_inc_ref(v_arg_2601_);
lean_dec_ref_known(v_x_2592_, 2);
v___x_2602_ = lean_array_set(v_x_2593_, v_x_2594_, v_arg_2601_);
v___x_2603_ = lean_unsigned_to_nat(1u);
v___x_2604_ = lean_nat_sub(v_x_2594_, v___x_2603_);
v___x_2605_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2588_, v_val_2586_, v_mvarId_2587_, v_majorFVarId_2589_, v_givenNames_2590_, v_recursorName_2591_, v_fn_2600_, v___x_2602_, v___x_2604_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2605_;
}
else
{
uint8_t v_depElim_2606_; lean_object* v_paramsPos_2607_; lean_object* v___x_2608_; 
lean_dec_ref(v_x_2592_);
v_depElim_2606_ = lean_ctor_get_uint8(v_a_2588_, sizeof(void*)*8);
v_paramsPos_2607_ = lean_ctor_get(v_a_2588_, 5);
lean_inc(v_paramsPos_2607_);
lean_inc(v_mvarId_2587_);
lean_inc_ref(v_val_2586_);
v___x_2608_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2593_, v_val_2586_, v_mvarId_2587_, v_paramsPos_2607_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v_x_2593_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v___x_2609_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; size_t v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___x_2627_; 
lean_dec_ref_known(v___x_2608_, 1);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2588_);
lean_inc(v_mvarId_2587_);
v___x_2627_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2587_, v___x_2609_, v_a_2588_, v_val_2586_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
lean_inc(v_mvarId_2587_);
v___x_2629_ = l_Lean_MVarId_getType(v_mvarId_2587_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v_cls_2631_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v_cls_2631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2606_ == 0)
{
lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2743_; 
lean_inc(v_majorFVarId_2589_);
v___x_2720_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2630_, v_majorFVarId_2589_, v___y_2596_);
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
lean_dec(v_recursorName_2591_);
v___y_2633_ = v___y_2595_;
v___y_2634_ = v___y_2596_;
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2726_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2727_ = l_Lean_MessageData_ofName(v_recursorName_2591_);
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
lean_inc(v_mvarId_2587_);
v___x_2733_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2609_, v_mvarId_2587_, v___x_2732_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
v___y_2633_ = v___y_2595_;
v___y_2634_ = v___y_2596_;
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
goto v___jp_2632_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2628_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_mvarId_2587_);
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
lean_dec(v_a_2630_);
lean_dec(v_recursorName_2591_);
v___y_2633_ = v___y_2595_;
v___y_2634_ = v___y_2596_;
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
goto v___jp_2632_;
}
v___jp_2632_:
{
size_t v_sz_2637_; size_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; 
v_sz_2637_ = lean_array_size(v_a_2628_);
v___x_2638_ = ((size_t)0ULL);
lean_inc(v_a_2628_);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2637_, v___x_2638_, v_a_2628_);
lean_inc(v_majorFVarId_2589_);
v___x_2640_ = lean_array_push(v___x_2639_, v_majorFVarId_2589_);
v___x_2641_ = 1;
v___x_2642_ = 0;
v___x_2643_ = l_Lean_MVarId_revert(v_mvarId_2587_, v___x_2640_, v___x_2641_, v___x_2642_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v_fst_2645_ = lean_ctor_get(v_a_2644_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v_a_2644_, 1);
lean_inc(v_snd_2646_);
lean_dec(v_a_2644_);
v___x_2647_ = lean_array_get_size(v_a_2628_);
v___x_2648_ = lean_box(0);
v___x_2649_ = l_Lean_Meta_introNCore(v_snd_2646_, v___x_2647_, v___x_2648_, v___x_2642_, v___x_2641_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2653_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v_fst_2651_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_fst_2651_);
v_snd_2652_ = lean_ctor_get(v_a_2650_, 1);
lean_inc(v_snd_2652_);
lean_dec(v_a_2650_);
v___x_2653_ = l_Lean_Meta_intro1Core(v_snd_2652_, v___x_2641_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2695_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v_fst_2655_ = lean_ctor_get(v_a_2654_, 0);
v_snd_2656_ = lean_ctor_get(v_a_2654_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2658_ = v_a_2654_;
v_isShared_2659_ = v_isSharedCheck_2695_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_inc(v_fst_2655_);
lean_dec(v_a_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2695_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2660_ = lean_box(0);
lean_inc(v_fst_2655_);
v___x_2661_ = l_Lean_mkFVar(v_fst_2655_);
lean_inc_ref(v___x_2661_);
v___x_2662_ = l_Lean_Meta_FVarSubst_insert(v___x_2660_, v_majorFVarId_2589_, v___x_2661_);
v___x_2663_ = lean_unsigned_to_nat(0u);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2663_);
lean_ctor_set(v___x_2658_, 0, v___x_2662_);
v___x_2665_ = v___x_2658_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v_toCold_2667_; lean_object* v_options_2668_; uint8_t v_hasTrace_2669_; 
v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2651_, v_a_2628_, v_sz_2637_, v___x_2638_, v___x_2665_);
lean_dec(v_a_2628_);
v_toCold_2667_ = lean_ctor_get(v___y_2635_, 0);
v_options_2668_ = lean_ctor_get(v_toCold_2667_, 2);
v_hasTrace_2669_ = lean_ctor_get_uint8(v_options_2668_, sizeof(void*)*1);
if (v_hasTrace_2669_ == 0)
{
lean_object* v_fst_2670_; 
v_fst_2670_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_fst_2670_);
lean_dec_ref(v___x_2666_);
lean_inc(v_snd_2656_);
v___y_2611_ = v_snd_2656_;
v___y_2612_ = v_fst_2670_;
v___y_2613_ = v_fst_2645_;
v___y_2614_ = v_fst_2655_;
v___y_2615_ = v___x_2661_;
v___y_2616_ = v_snd_2656_;
v___y_2617_ = v_fst_2651_;
v___y_2618_ = v___x_2638_;
v___y_2619_ = v___y_2633_;
v___y_2620_ = v___y_2634_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
goto v___jp_2610_;
}
else
{
lean_object* v_fst_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2692_; 
v_fst_2671_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2666_, 1);
lean_dec(v_unused_2693_);
v___x_2673_ = v___x_2666_;
v_isShared_2674_ = v_isSharedCheck_2692_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_fst_2671_);
lean_dec(v___x_2666_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2692_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_inheritedTraceOptions_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_inheritedTraceOptions_2675_ = lean_ctor_get(v_toCold_2667_, 11);
v___x_2676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2677_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2675_, v_options_2668_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_del_object(v___x_2673_);
lean_inc(v_snd_2656_);
v___y_2611_ = v_snd_2656_;
v___y_2612_ = v_fst_2671_;
v___y_2613_ = v_fst_2645_;
v___y_2614_ = v_fst_2655_;
v___y_2615_ = v___x_2661_;
v___y_2616_ = v_snd_2656_;
v___y_2617_ = v_fst_2651_;
v___y_2618_ = v___x_2638_;
v___y_2619_ = v___y_2633_;
v___y_2620_ = v___y_2634_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2656_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_snd_2656_);
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
v___x_2682_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2631_, v___x_2681_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_dec_ref_known(v___x_2682_, 1);
lean_inc(v_snd_2656_);
v___y_2611_ = v_snd_2656_;
v___y_2612_ = v_fst_2671_;
v___y_2613_ = v_fst_2645_;
v___y_2614_ = v_fst_2655_;
v___y_2615_ = v___x_2661_;
v___y_2616_ = v_snd_2656_;
v___y_2617_ = v_fst_2651_;
v___y_2618_ = v___x_2638_;
v___y_2619_ = v___y_2633_;
v___y_2620_ = v___y_2634_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_fst_2671_);
lean_dec_ref(v___x_2661_);
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_dec(v_fst_2651_);
lean_dec(v_fst_2645_);
lean_dec_ref(v_givenNames_2590_);
lean_dec_ref(v_a_2588_);
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
lean_dec(v_fst_2651_);
lean_dec(v_fst_2645_);
lean_dec(v_a_2628_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
v_a_2696_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2653_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2653_);
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
lean_dec(v_fst_2645_);
lean_dec(v_a_2628_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
v_a_2704_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2649_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2649_);
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
lean_dec(v_a_2628_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
v_a_2712_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2643_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2643_);
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
lean_dec(v_a_2628_);
lean_dec(v_recursorName_2591_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_mvarId_2587_);
v_a_2744_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2629_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2629_);
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
lean_dec(v_recursorName_2591_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_mvarId_2587_);
v_a_2752_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2627_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2627_);
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
v___jp_2610_:
{
size_t v_sz_2623_; lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; 
v_sz_2623_ = lean_array_size(v___y_2617_);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2623_, v___y_2618_, v___y_2617_);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2625_, 0, v___y_2611_);
lean_closure_set(v___f_2625_, 1, v___x_2609_);
lean_closure_set(v___f_2625_, 2, v___y_2614_);
lean_closure_set(v___f_2625_, 3, v_a_2588_);
lean_closure_set(v___f_2625_, 4, v___x_2624_);
lean_closure_set(v___f_2625_, 5, v_givenNames_2590_);
lean_closure_set(v___f_2625_, 6, v___y_2613_);
lean_closure_set(v___f_2625_, 7, v___y_2615_);
lean_closure_set(v___f_2625_, 8, v___y_2612_);
v___x_2626_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2616_, v___f_2625_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2626_;
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_recursorName_2591_);
lean_dec_ref(v_givenNames_2590_);
lean_dec(v_majorFVarId_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_mvarId_2587_);
lean_dec_ref(v_val_2586_);
v_a_2760_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2608_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2608_);
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
lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_toCold_2853_; lean_object* v_options_2854_; uint8_t v_hasTrace_2855_; 
v_toCold_2853_ = lean_ctor_get(v___y_2794_, 0);
v_options_2854_ = lean_ctor_get(v_toCold_2853_, 2);
v_hasTrace_2855_ = lean_ctor_get_uint8(v_options_2854_, sizeof(void*)*1);
if (v_hasTrace_2855_ == 0)
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
lean_object* v_inheritedTraceOptions_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_inheritedTraceOptions_2856_ = lean_ctor_get(v_toCold_2853_, 11);
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2791_);
v___x_2858_ = l_Lean_Name_append(v___x_2857_, v_cls_2791_);
v___x_2859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2856_, v_options_2854_, v___x_2858_);
lean_dec(v___x_2858_);
if (v___x_2859_ == 0)
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
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2860_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2787_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_mvarId_2787_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2791_, v___x_2862_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref_known(v___x_2863_, 1);
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
goto v___jp_2797_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
lean_dec(v_mvarId_2787_);
lean_dec_ref(v___x_2786_);
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
