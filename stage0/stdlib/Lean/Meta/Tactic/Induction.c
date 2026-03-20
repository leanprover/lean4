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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 58, 44, 222, 146, 107, 234, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "finalize loop is done, "};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "name of major premise: "};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8;
static const lean_array_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Tactic.Induction"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.Tactic.Induction.0.Lean.Meta.finalize.loop"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
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
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
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
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
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
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v___x_63_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_49_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
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
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
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
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
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
lean_inc(v_a_97_);
lean_inc_ref(v_a_96_);
lean_inc(v_a_95_);
lean_inc_ref(v_a_94_);
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
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
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
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v___x_111_;
}
}
}
else
{
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
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
lean_dec_ref(v_x_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(lean_object* v_cls_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_options_133_; uint8_t v_hasTrace_134_; 
v_options_133_ = lean_ctor_get(v___y_131_, 2);
v_hasTrace_134_ = lean_ctor_get_uint8(v_options_133_, sizeof(void*)*1);
if (v_hasTrace_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_cls_130_);
v___x_135_ = lean_box(v_hasTrace_134_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_inheritedTraceOptions_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_inheritedTraceOptions_137_ = lean_ctor_get(v___y_131_, 13);
v___x_138_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___closed__1));
v___x_139_ = l_Lean_Name_append(v___x_138_, v_cls_130_);
v___x_140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_137_, v_options_133_, v___x_139_);
lean_dec(v___x_139_);
v___x_141_ = lean_box(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg___boxed(lean_object* v_cls_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v_cls_143_, v___y_144_);
lean_dec_ref(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v_cls_147_, v___y_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___f_168_; lean_object* v___x_8119__overap_169_; lean_object* v___x_170_; 
v___f_168_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___closed__0));
v___x_8119__overap_169_ = lean_panic_fn(v___f_168_, v_msg_162_);
v___x_170_ = lean_apply_5(v___x_8119__overap_169_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3(lean_object* v_msgData_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; lean_object* v_env_185_; lean_object* v___x_186_; lean_object* v_mctx_187_; lean_object* v_lctx_188_; lean_object* v_options_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_184_ = lean_st_ref_get(v___y_182_);
v_env_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc_ref(v_env_185_);
lean_dec(v___x_184_);
v___x_186_ = lean_st_ref_get(v___y_180_);
v_mctx_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc_ref(v_mctx_187_);
lean_dec(v___x_186_);
v_lctx_188_ = lean_ctor_get(v___y_179_, 2);
v_options_189_ = lean_ctor_get(v___y_181_, 2);
lean_inc_ref(v_options_189_);
lean_inc_ref(v_lctx_188_);
v___x_190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_190_, 0, v_env_185_);
lean_ctor_set(v___x_190_, 1, v_mctx_187_);
lean_ctor_set(v___x_190_, 2, v_lctx_188_);
lean_ctor_set(v___x_190_, 3, v_options_189_);
v___x_191_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_msgData_178_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3___boxed(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3(v_msgData_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_199_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__0(void){
_start:
{
lean_object* v___x_200_; double v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_float_of_nat(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v_cls_205_, lean_object* v_msg_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_ref_212_; lean_object* v___x_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_258_; 
v_ref_212_ = lean_ctor_get(v___y_209_, 5);
v___x_213_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3(v_msg_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_258_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_258_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_258_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v_traceState_219_; lean_object* v_env_220_; lean_object* v_nextMacroScope_221_; lean_object* v_ngen_222_; lean_object* v_auxDeclNGen_223_; lean_object* v_cache_224_; lean_object* v_messages_225_; lean_object* v_infoState_226_; lean_object* v_snapshotTasks_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_257_; 
v___x_218_ = lean_st_ref_take(v___y_210_);
v_traceState_219_ = lean_ctor_get(v___x_218_, 4);
v_env_220_ = lean_ctor_get(v___x_218_, 0);
v_nextMacroScope_221_ = lean_ctor_get(v___x_218_, 1);
v_ngen_222_ = lean_ctor_get(v___x_218_, 2);
v_auxDeclNGen_223_ = lean_ctor_get(v___x_218_, 3);
v_cache_224_ = lean_ctor_get(v___x_218_, 5);
v_messages_225_ = lean_ctor_get(v___x_218_, 6);
v_infoState_226_ = lean_ctor_get(v___x_218_, 7);
v_snapshotTasks_227_ = lean_ctor_get(v___x_218_, 8);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_257_ == 0)
{
v___x_229_ = v___x_218_;
v_isShared_230_ = v_isSharedCheck_257_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_snapshotTasks_227_);
lean_inc(v_infoState_226_);
lean_inc(v_messages_225_);
lean_inc(v_cache_224_);
lean_inc(v_traceState_219_);
lean_inc(v_auxDeclNGen_223_);
lean_inc(v_ngen_222_);
lean_inc(v_nextMacroScope_221_);
lean_inc(v_env_220_);
lean_dec(v___x_218_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_257_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
uint64_t v_tid_231_; lean_object* v_traces_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_256_; 
v_tid_231_ = lean_ctor_get_uint64(v_traceState_219_, sizeof(void*)*1);
v_traces_232_ = lean_ctor_get(v_traceState_219_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_traceState_219_);
if (v_isSharedCheck_256_ == 0)
{
v___x_234_ = v_traceState_219_;
v_isShared_235_ = v_isSharedCheck_256_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_traces_232_);
lean_dec(v_traceState_219_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_256_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; double v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_236_ = lean_box(0);
v___x_237_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__0);
v___x_238_ = 0;
v___x_239_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__1));
v___x_240_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_240_, 0, v_cls_205_);
lean_ctor_set(v___x_240_, 1, v___x_236_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
lean_ctor_set_float(v___x_240_, sizeof(void*)*3, v___x_237_);
lean_ctor_set_float(v___x_240_, sizeof(void*)*3 + 8, v___x_237_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*3 + 16, v___x_238_);
v___x_241_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___closed__2));
v___x_242_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v_a_214_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
lean_inc(v_ref_212_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_ref_212_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_PersistentArray_push___redArg(v_traces_232_, v___x_243_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_244_);
v___x_246_ = v___x_234_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_244_);
lean_ctor_set_uint64(v_reuseFailAlloc_255_, sizeof(void*)*1, v_tid_231_);
v___x_246_ = v_reuseFailAlloc_255_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_248_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v___x_246_);
v___x_248_ = v___x_229_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_env_220_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_nextMacroScope_221_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_ngen_222_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_auxDeclNGen_223_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_254_, 5, v_cache_224_);
lean_ctor_set(v_reuseFailAlloc_254_, 6, v_messages_225_);
lean_ctor_set(v_reuseFailAlloc_254_, 7, v_infoState_226_);
lean_ctor_set(v_reuseFailAlloc_254_, 8, v_snapshotTasks_227_);
v___x_248_ = v_reuseFailAlloc_254_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_st_ref_set(v___y_210_, v___x_248_);
v___x_250_ = lean_box(0);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_250_);
v___x_252_ = v___x_216_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v_cls_259_, lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v_cls_259_, v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(size_t v_sz_267_, size_t v_i_268_, lean_object* v_bs_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = lean_usize_dec_lt(v_i_268_, v_sz_267_);
if (v___x_270_ == 0)
{
return v_bs_269_;
}
else
{
lean_object* v_v_271_; lean_object* v___x_272_; lean_object* v_bs_x27_273_; lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v_v_271_ = lean_array_uget(v_bs_269_, v_i_268_);
v___x_272_ = lean_unsigned_to_nat(0u);
v_bs_x27_273_ = lean_array_uset(v_bs_269_, v_i_268_, v___x_272_);
v___x_274_ = l_Lean_mkFVar(v_v_271_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_268_, v___x_275_);
v___x_277_ = lean_array_uset(v_bs_x27_273_, v_i_268_, v___x_274_);
v_i_268_ = v___x_276_;
v_bs_269_ = v___x_277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(lean_object* v_sz_279_, lean_object* v_i_280_, lean_object* v_bs_281_){
_start:
{
size_t v_sz_boxed_282_; size_t v_i_boxed_283_; lean_object* v_res_284_; 
v_sz_boxed_282_ = lean_unbox_usize(v_sz_279_);
lean_dec(v_sz_279_);
v_i_boxed_283_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_sz_boxed_282_, v_i_boxed_283_, v_bs_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9_spec__10___redArg(lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_ks_289_; lean_object* v_vs_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_314_; 
v_ks_289_ = lean_ctor_get(v_x_285_, 0);
v_vs_290_ = lean_ctor_get(v_x_285_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_314_ == 0)
{
v___x_292_ = v_x_285_;
v_isShared_293_ = v_isSharedCheck_314_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_vs_290_);
lean_inc(v_ks_289_);
lean_dec(v_x_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_314_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_ks_289_);
v___x_295_ = lean_nat_dec_lt(v_x_286_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec(v_x_286_);
v___x_296_ = lean_array_push(v_ks_289_, v_x_287_);
v___x_297_ = lean_array_push(v_vs_290_, v_x_288_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_297_);
lean_ctor_set(v___x_292_, 0, v___x_296_);
v___x_299_ = v___x_292_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
lean_object* v_k_x27_301_; uint8_t v___x_302_; 
v_k_x27_301_ = lean_array_fget_borrowed(v_ks_289_, v_x_286_);
v___x_302_ = l_Lean_instBEqMVarId_beq(v_x_287_, v_k_x27_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_304_; 
if (v_isShared_293_ == 0)
{
v___x_304_ = v___x_292_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_ks_289_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_vs_290_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_x_286_, v___x_305_);
lean_dec(v_x_286_);
v_x_285_ = v___x_304_;
v_x_286_ = v___x_306_;
goto _start;
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_309_ = lean_array_fset(v_ks_289_, v_x_286_, v_x_287_);
v___x_310_ = lean_array_fset(v_vs_290_, v_x_286_, v_x_288_);
lean_dec(v_x_286_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_310_);
lean_ctor_set(v___x_292_, 0, v___x_309_);
v___x_312_ = v___x_292_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_n_315_, lean_object* v_k_316_, lean_object* v_v_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9_spec__10___redArg(v_n_315_, v___x_318_, v_k_316_, v_v_317_);
return v___x_319_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; 
v___x_320_ = ((size_t)5ULL);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_shift_left(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; 
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_325_ = lean_usize_sub(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(lean_object* v_x_327_, size_t v_x_328_, size_t v_x_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v_es_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v_j_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_es_332_ = lean_ctor_get(v_x_327_, 0);
v___x_333_ = ((size_t)5ULL);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_336_ = lean_usize_land(v_x_328_, v___x_335_);
v_j_337_ = lean_usize_to_nat(v___x_336_);
v___x_338_ = lean_array_get_size(v_es_332_);
v___x_339_ = lean_nat_dec_lt(v_j_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v_j_337_);
lean_dec(v_x_331_);
lean_dec(v_x_330_);
return v_x_327_;
}
else
{
lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_376_; 
lean_inc_ref(v_es_332_);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v_x_327_, 0);
lean_dec(v_unused_377_);
v___x_341_ = v_x_327_;
v_isShared_342_ = v_isSharedCheck_376_;
goto v_resetjp_340_;
}
else
{
lean_dec(v_x_327_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_376_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_v_343_; lean_object* v___x_344_; lean_object* v_xs_x27_345_; lean_object* v___y_347_; 
v_v_343_ = lean_array_fget(v_es_332_, v_j_337_);
v___x_344_ = lean_box(0);
v_xs_x27_345_ = lean_array_fset(v_es_332_, v_j_337_, v___x_344_);
switch(lean_obj_tag(v_v_343_))
{
case 0:
{
lean_object* v_key_352_; lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v_key_352_ = lean_ctor_get(v_v_343_, 0);
v_val_353_ = lean_ctor_get(v_v_343_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_v_343_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v_v_343_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_inc(v_key_352_);
lean_dec(v_v_343_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_instBEqMVarId_beq(v_x_330_, v_key_352_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_del_object(v___x_355_);
v___x_358_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_352_, v_val_353_, v_x_330_, v_x_331_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
v___y_347_ = v___x_359_;
goto v___jp_346_;
}
else
{
lean_object* v___x_361_; 
lean_dec(v_val_353_);
lean_dec(v_key_352_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v_x_331_);
lean_ctor_set(v___x_355_, 0, v_x_330_);
v___x_361_ = v___x_355_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_x_330_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_x_331_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v___y_347_ = v___x_361_;
goto v___jp_346_;
}
}
}
}
case 1:
{
lean_object* v_node_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
v_node_364_ = lean_ctor_get(v_v_343_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_v_343_);
if (v_isSharedCheck_374_ == 0)
{
v___x_366_ = v_v_343_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_node_364_);
lean_dec(v_v_343_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_368_ = lean_usize_shift_right(v_x_328_, v___x_333_);
v___x_369_ = lean_usize_add(v_x_329_, v___x_334_);
v___x_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(v_node_364_, v___x_368_, v___x_369_, v_x_330_, v_x_331_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_370_);
v___x_372_ = v___x_366_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
v___y_347_ = v___x_372_;
goto v___jp_346_;
}
}
}
default: 
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_x_330_);
lean_ctor_set(v___x_375_, 1, v_x_331_);
v___y_347_ = v___x_375_;
goto v___jp_346_;
}
}
v___jp_346_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_array_fset(v_xs_x27_345_, v_j_337_, v___y_347_);
lean_dec(v_j_337_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_348_);
v___x_350_ = v___x_341_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
else
{
lean_object* v_ks_378_; lean_object* v_vs_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_399_; 
v_ks_378_ = lean_ctor_get(v_x_327_, 0);
v_vs_379_ = lean_ctor_get(v_x_327_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_399_ == 0)
{
v___x_381_ = v_x_327_;
v_isShared_382_ = v_isSharedCheck_399_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_vs_379_);
lean_inc(v_ks_378_);
lean_dec(v_x_327_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_399_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_ks_378_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_vs_379_);
v___x_384_ = v_reuseFailAlloc_398_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v_newNode_385_; uint8_t v___y_387_; size_t v___x_393_; uint8_t v___x_394_; 
v_newNode_385_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9___redArg(v___x_384_, v_x_330_, v_x_331_);
v___x_393_ = ((size_t)7ULL);
v___x_394_ = lean_usize_dec_le(v___x_393_, v_x_329_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_385_);
v___x_396_ = lean_unsigned_to_nat(4u);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
lean_dec(v___x_395_);
v___y_387_ = v___x_397_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___x_394_;
goto v___jp_386_;
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
lean_object* v_ks_388_; lean_object* v_vs_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_ks_388_ = lean_ctor_get(v_newNode_385_, 0);
lean_inc_ref(v_ks_388_);
v_vs_389_ = lean_ctor_get(v_newNode_385_, 1);
lean_inc_ref(v_vs_389_);
lean_dec_ref(v_newNode_385_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_392_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg(v_x_329_, v_ks_388_, v_vs_389_, v___x_390_, v___x_391_);
lean_dec_ref(v_vs_389_);
lean_dec_ref(v_ks_388_);
return v___x_392_;
}
else
{
return v_newNode_385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg(size_t v_depth_400_, lean_object* v_keys_401_, lean_object* v_vals_402_, lean_object* v_i_403_, lean_object* v_entries_404_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_array_get_size(v_keys_401_);
v___x_406_ = lean_nat_dec_lt(v_i_403_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v_i_403_);
return v_entries_404_;
}
else
{
lean_object* v_k_407_; lean_object* v_v_408_; uint64_t v___x_409_; size_t v_h_410_; size_t v___x_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v_h_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_k_407_ = lean_array_fget_borrowed(v_keys_401_, v_i_403_);
v_v_408_ = lean_array_fget_borrowed(v_vals_402_, v_i_403_);
v___x_409_ = l_Lean_instHashableMVarId_hash(v_k_407_);
v_h_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_sub(v_depth_400_, v___x_413_);
v___x_415_ = lean_usize_mul(v___x_411_, v___x_414_);
v_h_416_ = lean_usize_shift_right(v_h_410_, v___x_415_);
v___x_417_ = lean_nat_add(v_i_403_, v___x_412_);
lean_dec(v_i_403_);
lean_inc(v_v_408_);
lean_inc(v_k_407_);
v___x_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(v_entries_404_, v_h_416_, v_depth_400_, v_k_407_, v_v_408_);
v_i_403_ = v___x_417_;
v_entries_404_ = v___x_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_depth_420_, lean_object* v_keys_421_, lean_object* v_vals_422_, lean_object* v_i_423_, lean_object* v_entries_424_){
_start:
{
size_t v_depth_boxed_425_; lean_object* v_res_426_; 
v_depth_boxed_425_ = lean_unbox_usize(v_depth_420_);
lean_dec(v_depth_420_);
v_res_426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_boxed_425_, v_keys_421_, v_vals_422_, v_i_423_, v_entries_424_);
lean_dec_ref(v_vals_422_);
lean_dec_ref(v_keys_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
size_t v_x_9480__boxed_432_; size_t v_x_9481__boxed_433_; lean_object* v_res_434_; 
v_x_9480__boxed_432_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_x_9481__boxed_433_ = lean_unbox_usize(v_x_429_);
lean_dec(v_x_429_);
v_res_434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(v_x_427_, v_x_9480__boxed_432_, v_x_9481__boxed_433_, v_x_430_, v_x_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_438_ = l_Lean_instHashableMVarId_hash(v_x_436_);
v___x_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(v_x_435_, v___x_439_, v___x_440_, v_x_436_, v_x_437_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object* v_mvarId_442_, lean_object* v_val_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_mctx_447_; lean_object* v_cache_448_; lean_object* v_zetaDeltaFVarIds_449_; lean_object* v_postponed_450_; lean_object* v_diag_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_478_; 
v___x_446_ = lean_st_ref_take(v___y_444_);
v_mctx_447_ = lean_ctor_get(v___x_446_, 0);
v_cache_448_ = lean_ctor_get(v___x_446_, 1);
v_zetaDeltaFVarIds_449_ = lean_ctor_get(v___x_446_, 2);
v_postponed_450_ = lean_ctor_get(v___x_446_, 3);
v_diag_451_ = lean_ctor_get(v___x_446_, 4);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_478_ == 0)
{
v___x_453_ = v___x_446_;
v_isShared_454_ = v_isSharedCheck_478_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_diag_451_);
lean_inc(v_postponed_450_);
lean_inc(v_zetaDeltaFVarIds_449_);
lean_inc(v_cache_448_);
lean_inc(v_mctx_447_);
lean_dec(v___x_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_478_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_depth_455_; lean_object* v_levelAssignDepth_456_; lean_object* v_mvarCounter_457_; lean_object* v_lDepth_458_; lean_object* v_decls_459_; lean_object* v_userNames_460_; lean_object* v_lAssignment_461_; lean_object* v_eAssignment_462_; lean_object* v_dAssignment_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_477_; 
v_depth_455_ = lean_ctor_get(v_mctx_447_, 0);
v_levelAssignDepth_456_ = lean_ctor_get(v_mctx_447_, 1);
v_mvarCounter_457_ = lean_ctor_get(v_mctx_447_, 2);
v_lDepth_458_ = lean_ctor_get(v_mctx_447_, 3);
v_decls_459_ = lean_ctor_get(v_mctx_447_, 4);
v_userNames_460_ = lean_ctor_get(v_mctx_447_, 5);
v_lAssignment_461_ = lean_ctor_get(v_mctx_447_, 6);
v_eAssignment_462_ = lean_ctor_get(v_mctx_447_, 7);
v_dAssignment_463_ = lean_ctor_get(v_mctx_447_, 8);
v_isSharedCheck_477_ = !lean_is_exclusive(v_mctx_447_);
if (v_isSharedCheck_477_ == 0)
{
v___x_465_ = v_mctx_447_;
v_isShared_466_ = v_isSharedCheck_477_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_dAssignment_463_);
lean_inc(v_eAssignment_462_);
lean_inc(v_lAssignment_461_);
lean_inc(v_userNames_460_);
lean_inc(v_decls_459_);
lean_inc(v_lDepth_458_);
lean_inc(v_mvarCounter_457_);
lean_inc(v_levelAssignDepth_456_);
lean_inc(v_depth_455_);
lean_dec(v_mctx_447_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_477_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_462_, v_mvarId_442_, v_val_443_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 7, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_depth_455_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_levelAssignDepth_456_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_mvarCounter_457_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_lDepth_458_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_decls_459_);
lean_ctor_set(v_reuseFailAlloc_476_, 5, v_userNames_460_);
lean_ctor_set(v_reuseFailAlloc_476_, 6, v_lAssignment_461_);
lean_ctor_set(v_reuseFailAlloc_476_, 7, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_476_, 8, v_dAssignment_463_);
v___x_469_ = v_reuseFailAlloc_476_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_469_);
v___x_471_ = v___x_453_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_cache_448_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_zetaDeltaFVarIds_449_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_postponed_450_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_diag_451_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_st_ref_set(v___y_444_, v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_479_, lean_object* v_val_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_479_, v_val_480_, v___y_481_);
lean_dec(v___y_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg(lean_object* v___x_484_, lean_object* v_reverted_485_, lean_object* v_fst_486_, lean_object* v_n_487_, lean_object* v_j_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_zero_490_; uint8_t v_isZero_491_; 
v_zero_490_ = lean_unsigned_to_nat(0u);
v_isZero_491_ = lean_nat_dec_eq(v_j_488_, v_zero_490_);
if (v_isZero_491_ == 1)
{
lean_dec(v_j_488_);
return v_a_489_;
}
else
{
lean_object* v___x_492_; lean_object* v_n_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v_n_493_ = lean_nat_sub(v_j_488_, v___x_492_);
v___x_494_ = lean_nat_sub(v_n_487_, v_j_488_);
lean_dec(v_j_488_);
v___x_495_ = lean_nat_add(v___x_484_, v___x_492_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
lean_dec(v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_497_ = lean_array_fget_borrowed(v_reverted_485_, v___x_494_);
v___x_498_ = lean_box(0);
v___x_499_ = lean_nat_sub(v___x_494_, v___x_484_);
lean_dec(v___x_494_);
v___x_500_ = lean_nat_sub(v___x_499_, v___x_492_);
lean_dec(v___x_499_);
v___x_501_ = lean_array_get_borrowed(v___x_498_, v_fst_486_, v___x_500_);
lean_dec(v___x_500_);
lean_inc(v___x_501_);
v___x_502_ = l_Lean_mkFVar(v___x_501_);
lean_inc(v___x_497_);
v___x_503_ = l_Lean_Meta_FVarSubst_insert(v_a_489_, v___x_497_, v___x_502_);
v_j_488_ = v_n_493_;
v_a_489_ = v___x_503_;
goto _start;
}
else
{
lean_dec(v___x_494_);
v_j_488_ = v_n_493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg___boxed(lean_object* v___x_506_, lean_object* v_reverted_507_, lean_object* v_fst_508_, lean_object* v_n_509_, lean_object* v_j_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg(v___x_506_, v_reverted_507_, v_fst_508_, v_n_509_, v_j_510_, v_a_511_);
lean_dec(v_n_509_);
lean_dec_ref(v_fst_508_);
lean_dec_ref(v_reverted_507_);
lean_dec(v___x_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6(lean_object* v_mvarId_513_, lean_object* v_as_514_, size_t v_i_515_, size_t v_stop_516_, lean_object* v_b_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = lean_usize_dec_eq(v_i_515_, v_stop_516_);
if (v___x_523_ == 0)
{
lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_547_; 
v_fst_524_ = lean_ctor_get(v_b_517_, 0);
v_snd_525_ = lean_ctor_get(v_b_517_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_b_517_);
if (v_isSharedCheck_547_ == 0)
{
v___x_527_ = v_b_517_;
v_isShared_528_ = v_isSharedCheck_547_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snd_525_);
lean_inc(v_fst_524_);
lean_dec(v_b_517_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_547_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_array_uget_borrowed(v_as_514_, v_i_515_);
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v_mvarId_513_);
v___x_530_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_513_, v_snd_525_, v___x_529_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref(v___x_530_);
lean_inc(v___x_529_);
v___x_532_ = l_Lean_Expr_app___override(v_fst_524_, v___x_529_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v_a_531_);
lean_ctor_set(v___x_527_, 0, v___x_532_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_531_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
size_t v___x_535_; size_t v___x_536_; 
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_515_, v___x_535_);
v_i_515_ = v___x_536_;
v_b_517_ = v___x_534_;
goto _start;
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_527_);
lean_dec(v_fst_524_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v_mvarId_513_);
v_a_539_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_530_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_object* v___x_548_; 
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v_mvarId_513_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_b_517_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6___boxed(lean_object* v_mvarId_549_, lean_object* v_as_550_, lean_object* v_i_551_, lean_object* v_stop_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
size_t v_i_boxed_559_; size_t v_stop_boxed_560_; lean_object* v_res_561_; 
v_i_boxed_559_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_stop_boxed_560_ = lean_unbox_usize(v_stop_552_);
lean_dec(v_stop_552_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6(v_mvarId_549_, v_as_550_, v_i_boxed_559_, v_stop_boxed_560_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec_ref(v_as_550_);
return v_res_561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_583_ = lean_unsigned_to_nat(15u);
v___x_584_ = lean_unsigned_to_nat(120u);
v___x_585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11));
v___x_586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_587_ = l_mkPanicMessageWithDecl(v___x_586_, v___x_585_, v___x_584_, v___x_583_, v___x_582_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_588_, lean_object* v_givenNames_589_, lean_object* v_recursorInfo_590_, lean_object* v_reverted_591_, lean_object* v_major_592_, lean_object* v_indices_593_, lean_object* v_baseSubst_594_, lean_object* v_initialArity_595_, lean_object* v_numMinors_596_, lean_object* v_pos_597_, lean_object* v_minorIdx_598_, lean_object* v_recursor_599_, lean_object* v_recursorType_600_, uint8_t v_consumedMajor_601_, lean_object* v_subgoals_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___y_750_; lean_object* v___y_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; uint8_t v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___x_784_; 
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
v___x_784_ = l_Lean_Meta_whnfForall(v_recursorType_600_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; uint8_t v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; uint8_t v___y_876_; uint8_t v___y_877_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; uint8_t v___y_953_; uint8_t v___y_954_; lean_object* v___y_955_; lean_object* v___y_961_; uint8_t v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; uint8_t v___y_978_; uint8_t v___x_1025_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v___x_1025_ = l_Lean_Expr_isForall(v_a_785_);
if (v___x_1025_ == 0)
{
v___y_978_ = v___x_1025_;
goto v___jp_977_;
}
else
{
lean_object* v_numArgs_1026_; uint8_t v___x_1027_; 
v_numArgs_1026_ = lean_ctor_get(v_recursorInfo_590_, 3);
v___x_1027_ = lean_nat_dec_lt(v_pos_597_, v_numArgs_1026_);
v___y_978_ = v___x_1027_;
goto v___jp_977_;
}
v___jp_786_:
{
lean_object* v___x_801_; 
lean_inc_ref(v___y_795_);
v___x_801_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_787_, v___y_792_, v___y_795_, v___y_793_, v___y_798_, v___y_796_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
lean_inc(v___y_796_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_793_);
lean_inc_ref(v___y_795_);
lean_inc(v_mvarId_588_);
v___x_803_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_588_, v_a_785_, v_a_802_, v___y_795_, v___y_793_, v___y_798_, v___y_796_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v___x_805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_806_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v___x_805_, v___y_798_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
lean_inc(v_a_802_);
v___x_808_ = l_Lean_Expr_app___override(v_recursor_599_, v_a_802_);
v___x_809_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
if (v___x_809_ == 0)
{
v___y_718_ = v___y_788_;
v___y_719_ = v_a_802_;
v___y_720_ = v___y_789_;
v___y_721_ = v___y_790_;
v___y_722_ = v___x_808_;
v___y_723_ = v___y_797_;
v___y_724_ = v___y_791_;
v___y_725_ = v_a_804_;
v___y_726_ = v___y_800_;
v___y_727_ = v___y_799_;
v___y_728_ = v___y_794_;
v___y_729_ = v___y_795_;
v___y_730_ = v___y_793_;
v___y_731_ = v___y_798_;
v___y_732_ = v___y_796_;
goto v___jp_717_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8);
v___x_811_ = l_Lean_Expr_fvarId_x21(v_major_592_);
v___x_812_ = l_Lean_MessageData_ofName(v___x_811_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_810_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_805_, v___x_813_, v___y_795_, v___y_793_, v___y_798_, v___y_796_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref(v___x_814_);
v___y_718_ = v___y_788_;
v___y_719_ = v_a_802_;
v___y_720_ = v___y_789_;
v___y_721_ = v___y_790_;
v___y_722_ = v___x_808_;
v___y_723_ = v___y_797_;
v___y_724_ = v___y_791_;
v___y_725_ = v_a_804_;
v___y_726_ = v___y_800_;
v___y_727_ = v___y_799_;
v___y_728_ = v___y_794_;
v___y_729_ = v___y_795_;
v___y_730_ = v___y_793_;
v___y_731_ = v___y_798_;
v___y_732_ = v___y_796_;
goto v___jp_717_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v___x_808_);
lean_dec(v_a_804_);
lean_dec(v_a_802_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_793_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_788_);
lean_dec_ref(v_subgoals_602_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_a_804_);
lean_dec(v_a_802_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_793_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_788_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_823_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_806_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_806_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_802_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_793_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_788_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_831_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_803_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_803_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_793_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_788_);
lean_dec(v_a_785_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_839_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_801_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_801_);
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
v___jp_847_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_858_ = lean_nat_sub(v___y_849_, v_initialArity_595_);
lean_dec(v___y_849_);
v___x_859_ = lean_array_get_size(v_reverted_591_);
v___x_860_ = lean_array_get_size(v_indices_593_);
v___x_861_ = lean_nat_sub(v___x_859_, v___x_860_);
v___x_862_ = lean_nat_sub(v___x_861_, v___y_851_);
lean_dec(v___x_861_);
v___x_863_ = lean_array_get_size(v_givenNames_589_);
v___x_864_ = lean_nat_dec_lt(v_minorIdx_598_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_box(0);
v___x_866_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*1, v___y_850_);
v___y_787_ = v___y_848_;
v___y_788_ = v___x_862_;
v___y_789_ = v___y_850_;
v___y_790_ = v___x_858_;
v___y_791_ = v___x_859_;
v___y_792_ = v___y_852_;
v___y_793_ = v___y_855_;
v___y_794_ = v___y_853_;
v___y_795_ = v___y_854_;
v___y_796_ = v___y_857_;
v___y_797_ = v___y_851_;
v___y_798_ = v___y_856_;
v___y_799_ = v___x_860_;
v___y_800_ = v___x_866_;
goto v___jp_786_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_array_fget_borrowed(v_givenNames_589_, v_minorIdx_598_);
lean_inc(v___x_867_);
v___y_787_ = v___y_848_;
v___y_788_ = v___x_862_;
v___y_789_ = v___y_850_;
v___y_790_ = v___x_858_;
v___y_791_ = v___x_859_;
v___y_792_ = v___y_852_;
v___y_793_ = v___y_855_;
v___y_794_ = v___y_853_;
v___y_795_ = v___y_854_;
v___y_796_ = v___y_857_;
v___y_797_ = v___y_851_;
v___y_798_ = v___y_856_;
v___y_799_ = v___x_860_;
v___y_800_ = v___x_867_;
goto v___jp_786_;
}
}
v___jp_868_:
{
if (v___y_877_ == 0)
{
lean_object* v___x_878_; uint8_t v___x_879_; 
lean_inc_ref(v___y_869_);
v___x_878_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_869_);
v___x_879_ = lean_nat_dec_lt(v___x_878_, v_initialArity_595_);
if (v___x_879_ == 0)
{
v___y_848_ = v___y_869_;
v___y_849_ = v___x_878_;
v___y_850_ = v___y_877_;
v___y_851_ = v___y_870_;
v___y_852_ = v___y_872_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_871_;
v___y_855_ = v___y_875_;
v___y_856_ = v___y_874_;
v___y_857_ = v___y_873_;
goto v___jp_847_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_588_);
v___x_882_ = l_Lean_Meta_throwTacticEx___redArg(v___x_880_, v_mvarId_588_, v___x_881_, v___y_871_, v___y_875_, v___y_874_, v___y_873_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_dec_ref(v___x_882_);
v___y_848_ = v___y_869_;
v___y_849_ = v___x_878_;
v___y_850_ = v___y_877_;
v___y_851_ = v___y_870_;
v___y_852_ = v___y_872_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_871_;
v___y_855_ = v___y_875_;
v___y_856_ = v___y_874_;
v___y_857_ = v___y_873_;
goto v___jp_847_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v___x_878_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_869_);
lean_dec(v_a_785_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_box(0);
lean_inc(v___y_873_);
lean_inc_ref(v___y_874_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_871_);
lean_inc_ref(v___y_869_);
v___x_892_ = l_Lean_Meta_synthInstance_x3f(v___y_869_, v___x_891_, v___y_871_, v___y_875_, v___y_874_, v___y_873_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_892_);
if (lean_obj_tag(v_a_893_) == 0)
{
lean_object* v___x_894_; 
lean_inc_ref(v___y_871_);
v___x_894_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_869_, v___y_872_, v___y_871_, v___y_875_, v___y_874_, v___y_873_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
lean_inc(v___y_873_);
lean_inc_ref(v___y_874_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_871_);
lean_inc(v_mvarId_588_);
v___x_896_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_588_, v_a_785_, v_a_895_, v___y_871_, v___y_875_, v___y_874_, v___y_873_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_896_);
lean_inc(v_a_895_);
v___x_898_ = l_Lean_Expr_app___override(v_recursor_599_, v_a_895_);
v___x_899_ = lean_nat_add(v_pos_597_, v___y_870_);
lean_dec(v_pos_597_);
v___x_900_ = lean_nat_add(v_minorIdx_598_, v___y_870_);
lean_dec(v_minorIdx_598_);
v___x_901_ = l_Lean_Expr_mvarId_x21(v_a_895_);
lean_dec(v_a_895_);
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9));
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
lean_ctor_set(v___x_904_, 2, v___x_903_);
v___x_905_ = lean_array_push(v_subgoals_602_, v___x_904_);
v_pos_597_ = v___x_899_;
v_minorIdx_598_ = v___x_900_;
v_recursor_599_ = v___x_898_;
v_recursorType_600_ = v_a_897_;
v_subgoals_602_ = v___x_905_;
v_a_603_ = v___y_871_;
v_a_604_ = v___y_875_;
v_a_605_ = v___y_874_;
v_a_606_ = v___y_873_;
goto _start;
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_a_895_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_907_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_896_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_896_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_871_);
lean_dec(v_a_785_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_915_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_894_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_894_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_val_923_; lean_object* v___x_924_; 
lean_dec(v___y_872_);
lean_dec_ref(v___y_869_);
v_val_923_ = lean_ctor_get(v_a_893_, 0);
lean_inc(v_val_923_);
lean_dec_ref(v_a_893_);
lean_inc(v___y_873_);
lean_inc_ref(v___y_874_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_871_);
lean_inc(v_mvarId_588_);
v___x_924_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_588_, v_a_785_, v_val_923_, v___y_871_, v___y_875_, v___y_874_, v___y_873_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_Expr_app___override(v_recursor_599_, v_val_923_);
v___x_927_ = lean_nat_add(v_pos_597_, v___y_870_);
lean_dec(v_pos_597_);
v___x_928_ = lean_nat_add(v_minorIdx_598_, v___y_870_);
lean_dec(v_minorIdx_598_);
v_pos_597_ = v___x_927_;
v_minorIdx_598_ = v___x_928_;
v_recursor_599_ = v___x_926_;
v_recursorType_600_ = v_a_925_;
v_a_603_ = v___y_871_;
v_a_604_ = v___y_875_;
v_a_605_ = v___y_874_;
v_a_606_ = v___y_873_;
goto _start;
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_val_923_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_930_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_924_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_924_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_869_);
lean_dec(v_a_785_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_938_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_892_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_892_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
v___jp_946_:
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_BinderInfo_isInstImplicit(v___y_953_);
if (v___x_956_ == 0)
{
v___y_869_ = v___y_947_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_949_;
v___y_872_ = v___y_955_;
v___y_873_ = v___y_950_;
v___y_874_ = v___y_951_;
v___y_875_ = v___y_952_;
v___y_876_ = v___y_954_;
v___y_877_ = v___x_956_;
goto v___jp_868_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = lean_array_get_size(v_givenNames_589_);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_nat_dec_eq(v___x_957_, v___x_958_);
v___y_869_ = v___y_947_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_949_;
v___y_872_ = v___y_955_;
v___y_873_ = v___y_950_;
v___y_874_ = v___y_951_;
v___y_875_ = v___y_952_;
v___y_876_ = v___y_954_;
v___y_877_ = v___x_959_;
goto v___jp_868_;
}
}
v___jp_960_:
{
if (lean_obj_tag(v_a_785_) == 7)
{
lean_object* v_binderName_967_; lean_object* v_binderType_968_; uint8_t v_binderInfo_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_binderName_967_ = lean_ctor_get(v_a_785_, 0);
v_binderType_968_ = lean_ctor_get(v_a_785_, 1);
v_binderInfo_969_ = lean_ctor_get_uint8(v_a_785_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_968_);
v___x_970_ = l_Lean_Expr_headBeta(v_binderType_968_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_dec_eq(v_numMinors_596_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc(v_binderName_967_);
v___x_973_ = lean_erase_macro_scopes(v_binderName_967_);
v___x_974_ = l_Lean_Name_append(v___y_961_, v___x_973_);
v___y_947_ = v___x_970_;
v___y_948_ = v___x_971_;
v___y_949_ = v___y_963_;
v___y_950_ = v___y_966_;
v___y_951_ = v___y_965_;
v___y_952_ = v___y_964_;
v___y_953_ = v_binderInfo_969_;
v___y_954_ = v___y_962_;
v___y_955_ = v___x_974_;
goto v___jp_946_;
}
else
{
v___y_947_ = v___x_970_;
v___y_948_ = v___x_971_;
v___y_949_ = v___y_963_;
v___y_950_ = v___y_966_;
v___y_951_ = v___y_965_;
v___y_952_ = v___y_964_;
v___y_953_ = v_binderInfo_969_;
v___y_954_ = v___y_962_;
v___y_955_ = v___y_961_;
goto v___jp_946_;
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v___y_961_);
lean_dec(v_a_785_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13);
v___x_976_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v___x_975_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_976_;
}
}
v___jp_977_:
{
if (v___y_978_ == 0)
{
lean_dec(v_a_785_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
if (v_consumedMajor_601_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_588_);
v___x_981_ = l_Lean_Meta_throwTacticEx___redArg(v___x_979_, v_mvarId_588_, v___x_980_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_dec_ref(v___x_981_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_mvarId_588_);
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
}
else
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_590_);
v___x_991_ = lean_nat_dec_eq(v_pos_597_, v___x_990_);
lean_dec(v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_inc(v_mvarId_588_);
v___x_992_ = l_Lean_MVarId_getTag(v_mvarId_588_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; uint8_t v___x_994_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v___x_992_);
v___x_994_ = lean_nat_dec_le(v_numMinors_596_, v_minorIdx_598_);
if (v___x_994_ == 0)
{
v___y_961_ = v_a_993_;
v___y_962_ = v___y_978_;
v___y_963_ = v_a_603_;
v___y_964_ = v_a_604_;
v___y_965_ = v_a_605_;
v___y_966_ = v_a_606_;
goto v___jp_960_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_588_);
v___x_997_ = l_Lean_Meta_throwTacticEx___redArg(v___x_995_, v_mvarId_588_, v___x_996_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_dec_ref(v___x_997_);
v___y_961_ = v_a_993_;
v___y_962_ = v___y_978_;
v___y_963_ = v_a_603_;
v___y_964_ = v_a_604_;
v___y_965_ = v_a_605_;
v___y_966_ = v_a_606_;
goto v___jp_960_;
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_993_);
lean_dec(v_a_785_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_785_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_1006_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_992_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_992_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_array_get_size(v_indices_593_);
v___x_1016_ = lean_nat_dec_lt(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
v___y_750_ = v___x_991_;
v___y_751_ = v___x_1015_;
v_fst_752_ = v_recursor_599_;
v_snd_753_ = v_a_785_;
goto v___jp_749_;
}
else
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
lean_inc(v_a_785_);
lean_inc_ref(v_recursor_599_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v_recursor_599_);
lean_ctor_set(v___x_1017_, 1, v_a_785_);
v___x_1018_ = lean_nat_dec_le(v___x_1015_, v___x_1015_);
if (v___x_1018_ == 0)
{
if (v___x_1016_ == 0)
{
lean_dec_ref(v___x_1017_);
v___y_750_ = v___x_991_;
v___y_751_ = v___x_1015_;
v_fst_752_ = v_recursor_599_;
v_snd_753_ = v_a_785_;
goto v___jp_749_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v_a_785_);
lean_dec_ref(v_recursor_599_);
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1015_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
lean_inc(v_mvarId_588_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6(v_mvarId_588_, v_indices_593_, v___x_1019_, v___x_1020_, v___x_1017_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
v___y_770_ = v___x_991_;
v___y_771_ = v___x_1015_;
v___y_772_ = v___x_1021_;
goto v___jp_769_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v_a_785_);
lean_dec_ref(v_recursor_599_);
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1015_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
lean_inc(v_mvarId_588_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__6(v_mvarId_588_, v_indices_593_, v___x_1022_, v___x_1023_, v___x_1017_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
v___y_770_ = v___x_991_;
v___y_771_ = v___x_1015_;
v___y_772_ = v___x_1024_;
goto v___jp_769_;
}
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_subgoals_602_);
lean_dec_ref(v_recursor_599_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_1028_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_784_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_784_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
v___jp_608_:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_588_, v_recursor_599_, v___y_610_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref(v___x_613_);
v___x_614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_615_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v___x_614_, v___y_611_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_649_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_649_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_649_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_649_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_620_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_subgoals_602_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_subgoals_602_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_del_object(v___x_618_);
v___x_624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4);
v___x_625_ = lean_array_get_size(v_subgoals_602_);
v___x_626_ = l_Nat_reprFast(v___x_625_);
v___x_627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = l_Lean_MessageData_ofFormat(v___x_627_);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_624_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_614_, v___x_631_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_632_, 0);
lean_dec(v_unused_640_);
v___x_634_ = v___x_632_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___x_632_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_subgoals_602_);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_subgoals_602_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v_subgoals_602_);
v_a_641_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_632_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_632_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v_subgoals_602_);
v_a_650_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_615_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_615_);
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
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v_subgoals_602_);
v_a_658_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_613_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_613_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
v___jp_666_:
{
lean_object* v___x_683_; 
lean_inc(v___y_676_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_680_);
v___x_683_ = l_Lean_Meta_introNCore(v___y_670_, v___y_668_, v___y_671_, v___y_682_, v___y_669_, v___y_680_, v___y_679_, v___y_673_, v___y_676_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref(v___x_683_);
v_fst_685_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_fst_685_);
v_snd_686_ = lean_ctor_get(v_a_684_, 1);
lean_inc(v_snd_686_);
lean_dec(v_a_684_);
v___x_687_ = lean_box(0);
lean_inc(v___y_676_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_680_);
v___x_688_ = l_Lean_Meta_introNCore(v_snd_686_, v___y_667_, v___x_687_, v___y_669_, v___y_675_, v___y_680_, v___y_679_, v___y_673_, v___y_676_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_692_; size_t v_sz_693_; size_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___x_688_);
v_fst_690_ = lean_ctor_get(v_a_689_, 0);
lean_inc(v_fst_690_);
v_snd_691_ = lean_ctor_get(v_a_689_, 1);
lean_inc(v_snd_691_);
lean_dec(v_a_689_);
lean_inc(v_baseSubst_594_);
lean_inc(v___y_672_);
v___x_692_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg(v___y_681_, v_reverted_591_, v_fst_690_, v___y_672_, v___y_672_, v_baseSubst_594_);
lean_dec(v___y_672_);
lean_dec(v_fst_690_);
lean_dec(v___y_681_);
v_sz_693_ = lean_array_size(v_fst_685_);
v___x_694_ = ((size_t)0ULL);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_sz_693_, v___x_694_, v_fst_685_);
v___x_696_ = lean_nat_add(v_pos_597_, v___y_678_);
lean_dec(v_pos_597_);
v___x_697_ = lean_nat_add(v_minorIdx_598_, v___y_678_);
lean_dec(v_minorIdx_598_);
v___x_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_698_, 0, v_snd_691_);
lean_ctor_set(v___x_698_, 1, v___x_695_);
lean_ctor_set(v___x_698_, 2, v___x_692_);
v___x_699_ = lean_array_push(v_subgoals_602_, v___x_698_);
v_pos_597_ = v___x_696_;
v_minorIdx_598_ = v___x_697_;
v_recursor_599_ = v___y_677_;
v_recursorType_600_ = v___y_674_;
v_subgoals_602_ = v___x_699_;
v_a_603_ = v___y_680_;
v_a_604_ = v___y_679_;
v_a_605_ = v___y_673_;
v_a_606_ = v___y_676_;
goto _start;
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_fst_685_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_subgoals_602_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_701_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_688_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_688_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v___y_667_);
lean_dec_ref(v_subgoals_602_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_709_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_683_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_683_);
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
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = l_Lean_Expr_mvarId_x21(v___y_719_);
lean_dec_ref(v___y_719_);
v___x_734_ = l_Lean_Expr_fvarId_x21(v_major_592_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
v___x_735_ = l_Lean_MVarId_tryClear(v___x_733_, v___x_734_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_735_) == 0)
{
uint8_t v_explicit_736_; 
v_explicit_736_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*1);
if (v_explicit_736_ == 0)
{
lean_object* v_a_737_; lean_object* v_varNames_738_; 
v_a_737_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_735_);
v_varNames_738_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_varNames_738_);
lean_dec_ref(v___y_726_);
v___y_667_ = v___y_718_;
v___y_668_ = v___y_721_;
v___y_669_ = v___y_720_;
v___y_670_ = v_a_737_;
v___y_671_ = v_varNames_738_;
v___y_672_ = v___y_724_;
v___y_673_ = v___y_731_;
v___y_674_ = v___y_725_;
v___y_675_ = v___y_728_;
v___y_676_ = v___y_732_;
v___y_677_ = v___y_722_;
v___y_678_ = v___y_723_;
v___y_679_ = v___y_730_;
v___y_680_ = v___y_729_;
v___y_681_ = v___y_727_;
v___y_682_ = v___y_728_;
goto v___jp_666_;
}
else
{
lean_object* v_a_739_; lean_object* v_varNames_740_; 
v_a_739_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_735_);
v_varNames_740_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_varNames_740_);
lean_dec_ref(v___y_726_);
v___y_667_ = v___y_718_;
v___y_668_ = v___y_721_;
v___y_669_ = v___y_720_;
v___y_670_ = v_a_739_;
v___y_671_ = v_varNames_740_;
v___y_672_ = v___y_724_;
v___y_673_ = v___y_731_;
v___y_674_ = v___y_725_;
v___y_675_ = v___y_728_;
v___y_676_ = v___y_732_;
v___y_677_ = v___y_722_;
v___y_678_ = v___y_723_;
v___y_679_ = v___y_730_;
v___y_680_ = v___y_729_;
v___y_681_ = v___y_727_;
v___y_682_ = v___y_720_;
goto v___jp_666_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec(v___y_718_);
lean_dec_ref(v_subgoals_602_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_741_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_735_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_735_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_754_; 
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
lean_inc(v_mvarId_588_);
v___x_754_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_588_, v_snd_753_, v_major_592_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref(v___x_754_);
lean_inc_ref(v_major_592_);
v___x_756_ = l_Lean_Expr_app___override(v_fst_752_, v_major_592_);
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_pos_597_, v___x_757_);
lean_dec(v_pos_597_);
v___x_759_ = lean_nat_add(v___x_758_, v___y_751_);
lean_dec(v___y_751_);
lean_dec(v___x_758_);
v_pos_597_ = v___x_759_;
v_recursor_599_ = v___x_756_;
v_recursorType_600_ = v_a_755_;
v_consumedMajor_601_ = v___y_750_;
goto _start;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v_fst_752_);
lean_dec(v___y_751_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_subgoals_602_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_761_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_754_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_754_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
v___jp_769_:
{
if (lean_obj_tag(v___y_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_fst_774_; lean_object* v_snd_775_; 
v_a_773_ = lean_ctor_get(v___y_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___y_772_);
v_fst_774_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_fst_774_);
v_snd_775_ = lean_ctor_get(v_a_773_, 1);
lean_inc(v_snd_775_);
lean_dec(v_a_773_);
v___y_750_ = v___y_770_;
v___y_751_ = v___y_771_;
v_fst_752_ = v_fst_774_;
v_snd_753_ = v_snd_775_;
goto v___jp_749_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___y_771_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_subgoals_602_);
lean_dec(v_minorIdx_598_);
lean_dec(v_pos_597_);
lean_dec(v_baseSubst_594_);
lean_dec_ref(v_major_592_);
lean_dec(v_mvarId_588_);
v_a_776_ = lean_ctor_get(v___y_772_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___y_772_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___y_772_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___y_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_1036_ = _args[0];
lean_object* v_givenNames_1037_ = _args[1];
lean_object* v_recursorInfo_1038_ = _args[2];
lean_object* v_reverted_1039_ = _args[3];
lean_object* v_major_1040_ = _args[4];
lean_object* v_indices_1041_ = _args[5];
lean_object* v_baseSubst_1042_ = _args[6];
lean_object* v_initialArity_1043_ = _args[7];
lean_object* v_numMinors_1044_ = _args[8];
lean_object* v_pos_1045_ = _args[9];
lean_object* v_minorIdx_1046_ = _args[10];
lean_object* v_recursor_1047_ = _args[11];
lean_object* v_recursorType_1048_ = _args[12];
lean_object* v_consumedMajor_1049_ = _args[13];
lean_object* v_subgoals_1050_ = _args[14];
lean_object* v_a_1051_ = _args[15];
lean_object* v_a_1052_ = _args[16];
lean_object* v_a_1053_ = _args[17];
lean_object* v_a_1054_ = _args[18];
lean_object* v_a_1055_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1056_; lean_object* v_res_1057_; 
v_consumedMajor_boxed_1056_ = lean_unbox(v_consumedMajor_1049_);
v_res_1057_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1036_, v_givenNames_1037_, v_recursorInfo_1038_, v_reverted_1039_, v_major_1040_, v_indices_1041_, v_baseSubst_1042_, v_initialArity_1043_, v_numMinors_1044_, v_pos_1045_, v_minorIdx_1046_, v_recursor_1047_, v_recursorType_1048_, v_consumedMajor_boxed_1056_, v_subgoals_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_numMinors_1044_);
lean_dec(v_initialArity_1043_);
lean_dec_ref(v_indices_1041_);
lean_dec_ref(v_reverted_1039_);
lean_dec_ref(v_recursorInfo_1038_);
lean_dec_ref(v_givenNames_1037_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1058_, lean_object* v_val_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1058_, v_val_1059_, v___y_1061_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1066_, lean_object* v_val_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1066_, v_val_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(lean_object* v___x_1074_, lean_object* v_reverted_1075_, lean_object* v_fst_1076_, lean_object* v_n_1077_, lean_object* v_j_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___redArg(v___x_1074_, v_reverted_1075_, v_fst_1076_, v_n_1077_, v_j_1078_, v_a_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v___x_1082_, lean_object* v_reverted_1083_, lean_object* v_fst_1084_, lean_object* v_n_1085_, lean_object* v_j_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v___x_1082_, v_reverted_1083_, v_fst_1084_, v_n_1085_, v_j_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_n_1085_);
lean_dec_ref(v_fst_1084_);
lean_dec_ref(v_reverted_1083_);
lean_dec(v___x_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1091_, v_x_1092_, v_x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1095_, lean_object* v_x_1096_, size_t v_x_1097_, size_t v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___redArg(v_x_1096_, v_x_1097_, v_x_1098_, v_x_1099_, v_x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
size_t v_x_10827__boxed_1108_; size_t v_x_10828__boxed_1109_; lean_object* v_res_1110_; 
v_x_10827__boxed_1108_ = lean_unbox_usize(v_x_1104_);
lean_dec(v_x_1104_);
v_x_10828__boxed_1109_ = lean_unbox_usize(v_x_1105_);
lean_dec(v_x_1105_);
v_res_1110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3(v_00_u03b2_1102_, v_x_1103_, v_x_10827__boxed_1108_, v_x_10828__boxed_1109_, v_x_1106_, v_x_1107_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1111_, lean_object* v_n_1112_, lean_object* v_k_1113_, lean_object* v_v_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9___redArg(v_n_1112_, v_k_1113_, v_v_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1116_, size_t v_depth_1117_, lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_heq_1120_, lean_object* v_i_1121_, lean_object* v_entries_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_1117_, v_keys_1118_, v_vals_1119_, v_i_1121_, v_entries_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1124_, lean_object* v_depth_1125_, lean_object* v_keys_1126_, lean_object* v_vals_1127_, lean_object* v_heq_1128_, lean_object* v_i_1129_, lean_object* v_entries_1130_){
_start:
{
size_t v_depth_boxed_1131_; lean_object* v_res_1132_; 
v_depth_boxed_1131_ = lean_unbox_usize(v_depth_1125_);
lean_dec(v_depth_1125_);
v_res_1132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1124_, v_depth_boxed_1131_, v_keys_1126_, v_vals_1127_, v_heq_1128_, v_i_1129_, v_entries_1130_);
lean_dec_ref(v_vals_1127_);
lean_dec_ref(v_keys_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9_spec__10(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__3_spec__9_spec__10___redArg(v_x_1134_, v_x_1135_, v_x_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1141_, lean_object* v_givenNames_1142_, lean_object* v_recursorInfo_1143_, lean_object* v_reverted_1144_, lean_object* v_major_1145_, lean_object* v_indices_1146_, lean_object* v_baseSubst_1147_, lean_object* v_recursor_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; 
lean_inc(v_mvarId_1141_);
v___x_1154_ = l_Lean_MVarId_getType(v_mvarId_1141_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___x_1154_);
lean_inc(v_a_1152_);
lean_inc_ref(v_a_1151_);
lean_inc(v_a_1150_);
lean_inc_ref(v_a_1149_);
lean_inc_ref(v_recursor_1148_);
v___x_1156_ = lean_infer_type(v_recursor_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v_paramsPos_1158_; lean_object* v_produceMotive_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v_paramsPos_1158_ = lean_ctor_get(v_recursorInfo_1143_, 5);
v_produceMotive_1159_ = lean_ctor_get(v_recursorInfo_1143_, 7);
v___x_1160_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1155_);
v___x_1161_ = l_List_lengthTR___redArg(v_produceMotive_1159_);
v___x_1162_ = l_List_lengthTR___redArg(v_paramsPos_1158_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v___x_1162_, v___x_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = 0;
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1168_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1141_, v_givenNames_1142_, v_recursorInfo_1143_, v_reverted_1144_, v_major_1145_, v_indices_1146_, v_baseSubst_1147_, v___x_1160_, v___x_1161_, v___x_1164_, v___x_1165_, v_recursor_1148_, v_a_1157_, v___x_1166_, v___x_1167_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v___x_1161_);
lean_dec(v___x_1160_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_a_1155_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_recursor_1148_);
lean_dec(v_baseSubst_1147_);
lean_dec_ref(v_major_1145_);
lean_dec(v_mvarId_1141_);
v_a_1169_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1156_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1156_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_recursor_1148_);
lean_dec(v_baseSubst_1147_);
lean_dec_ref(v_major_1145_);
lean_dec(v_mvarId_1141_);
v_a_1177_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1154_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1154_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1185_, lean_object* v_givenNames_1186_, lean_object* v_recursorInfo_1187_, lean_object* v_reverted_1188_, lean_object* v_major_1189_, lean_object* v_indices_1190_, lean_object* v_baseSubst_1191_, lean_object* v_recursor_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1185_, v_givenNames_1186_, v_recursorInfo_1187_, v_reverted_1188_, v_major_1189_, v_indices_1190_, v_baseSubst_1191_, v_recursor_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec_ref(v_indices_1190_);
lean_dec_ref(v_reverted_1188_);
lean_dec_ref(v_recursorInfo_1187_);
lean_dec_ref(v_givenNames_1186_);
return v_res_1198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1202_, lean_object* v_mvarId_1203_, lean_object* v_majorType_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1211_ = l_Lean_indentExpr(v_majorType_1204_);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1202_, v_mvarId_1203_, v___x_1213_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1215_, lean_object* v_mvarId_1216_, lean_object* v_majorType_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1215_, v_mvarId_1216_, v_majorType_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1224_, lean_object* v_tacticName_1225_, lean_object* v_mvarId_1226_, lean_object* v_majorType_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1225_, v_mvarId_1226_, v_majorType_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_tacticName_1235_, lean_object* v_mvarId_1236_, lean_object* v_majorType_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1234_, v_tacticName_1235_, v_mvarId_1236_, v_majorType_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1244_, lean_object* v_x_1245_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = l_Lean_instBEqFVarId_beq(v_fvarId_1244_, v_x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1247_, v_x_1248_);
lean_dec(v_x_1248_);
lean_dec(v_fvarId_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1253_);
lean_dec(v_x_1253_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_unsigned_to_nat(16u);
v___x_1259_ = lean_mk_array(v___x_1258_, v___x_1257_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1263_, lean_object* v_fvarId_1264_, uint8_t v_generalizeNondepLet_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___y_1289_; lean_object* v___f_1293_; lean_object* v___f_1294_; 
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1293_, 0, v_fvarId_1264_);
v___f_1294_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1263_) == 0)
{
lean_object* v_type_1295_; lean_object* v___x_1296_; uint8_t v_fst_1298_; lean_object* v_mctx_1299_; lean_object* v___y_1317_; lean_object* v_mctx_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_type_1295_ = lean_ctor_get(v_localDecl_1263_, 3);
lean_inc_ref(v_type_1295_);
lean_dec_ref(v_localDecl_1263_);
v___x_1296_ = lean_st_ref_get(v___y_1266_);
v_mctx_1322_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref(v_mctx_1322_);
lean_dec(v___x_1296_);
v___x_1323_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_mctx_1322_);
v___x_1325_ = l_Lean_Expr_hasFVar(v_type_1295_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Expr_hasMVar(v_type_1295_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_type_1295_);
lean_dec_ref(v___f_1293_);
v_fst_1298_ = v___x_1326_;
v_mctx_1299_ = v_mctx_1322_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1327_; 
lean_dec_ref(v_mctx_1322_);
v___x_1327_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_type_1295_, v___x_1324_);
v___y_1317_ = v___x_1327_;
goto v___jp_1316_;
}
}
else
{
lean_object* v___x_1328_; 
lean_dec_ref(v_mctx_1322_);
v___x_1328_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_type_1295_, v___x_1324_);
v___y_1317_ = v___x_1328_;
goto v___jp_1316_;
}
v___jp_1297_:
{
lean_object* v___x_1300_; lean_object* v_cache_1301_; lean_object* v_zetaDeltaFVarIds_1302_; lean_object* v_postponed_1303_; lean_object* v_diag_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1314_; 
v___x_1300_ = lean_st_ref_take(v___y_1266_);
v_cache_1301_ = lean_ctor_get(v___x_1300_, 1);
v_zetaDeltaFVarIds_1302_ = lean_ctor_get(v___x_1300_, 2);
v_postponed_1303_ = lean_ctor_get(v___x_1300_, 3);
v_diag_1304_ = lean_ctor_get(v___x_1300_, 4);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1300_, 0);
lean_dec(v_unused_1315_);
v___x_1306_ = v___x_1300_;
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_diag_1304_);
lean_inc(v_postponed_1303_);
lean_inc(v_zetaDeltaFVarIds_1302_);
lean_inc(v_cache_1301_);
lean_dec(v___x_1300_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_mctx_1299_);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_mctx_1299_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_cache_1301_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_zetaDeltaFVarIds_1302_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_postponed_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_diag_1304_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_st_ref_set(v___y_1266_, v___x_1309_);
v___x_1311_ = lean_box(v_fst_1298_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
v___jp_1316_:
{
lean_object* v_snd_1318_; lean_object* v_fst_1319_; lean_object* v_mctx_1320_; uint8_t v___x_1321_; 
v_snd_1318_ = lean_ctor_get(v___y_1317_, 1);
lean_inc(v_snd_1318_);
v_fst_1319_ = lean_ctor_get(v___y_1317_, 0);
lean_inc(v_fst_1319_);
lean_dec_ref(v___y_1317_);
v_mctx_1320_ = lean_ctor_get(v_snd_1318_, 1);
lean_inc_ref(v_mctx_1320_);
lean_dec(v_snd_1318_);
v___x_1321_ = lean_unbox(v_fst_1319_);
lean_dec(v_fst_1319_);
v_fst_1298_ = v___x_1321_;
v_mctx_1299_ = v_mctx_1320_;
goto v___jp_1297_;
}
}
else
{
lean_object* v_type_1329_; lean_object* v_value_1330_; uint8_t v_nondep_1331_; uint8_t v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___y_1340_; 
v_type_1329_ = lean_ctor_get(v_localDecl_1263_, 3);
lean_inc_ref(v_type_1329_);
v_value_1330_ = lean_ctor_get(v_localDecl_1263_, 4);
lean_inc_ref(v_value_1330_);
v_nondep_1331_ = lean_ctor_get_uint8(v_localDecl_1263_, sizeof(void*)*5);
lean_dec_ref(v_localDecl_1263_);
if (v_generalizeNondepLet_1265_ == 0)
{
goto v___jp_1344_;
}
else
{
if (v_nondep_1331_ == 0)
{
goto v___jp_1344_;
}
else
{
lean_object* v___x_1353_; uint8_t v_fst_1355_; lean_object* v_mctx_1356_; lean_object* v___y_1374_; lean_object* v_mctx_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
lean_dec_ref(v_value_1330_);
v___x_1353_ = lean_st_ref_get(v___y_1266_);
v_mctx_1379_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_mctx_1379_);
lean_dec(v___x_1353_);
v___x_1380_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_1379_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v_mctx_1379_);
v___x_1382_ = l_Lean_Expr_hasFVar(v_type_1329_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Lean_Expr_hasMVar(v_type_1329_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v___x_1381_);
lean_dec_ref(v_type_1329_);
lean_dec_ref(v___f_1293_);
v_fst_1355_ = v___x_1383_;
v_mctx_1356_ = v_mctx_1379_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1384_; 
lean_dec_ref(v_mctx_1379_);
v___x_1384_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_type_1329_, v___x_1381_);
v___y_1374_ = v___x_1384_;
goto v___jp_1373_;
}
}
else
{
lean_object* v___x_1385_; 
lean_dec_ref(v_mctx_1379_);
v___x_1385_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_type_1329_, v___x_1381_);
v___y_1374_ = v___x_1385_;
goto v___jp_1373_;
}
v___jp_1354_:
{
lean_object* v___x_1357_; lean_object* v_cache_1358_; lean_object* v_zetaDeltaFVarIds_1359_; lean_object* v_postponed_1360_; lean_object* v_diag_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1371_; 
v___x_1357_ = lean_st_ref_take(v___y_1266_);
v_cache_1358_ = lean_ctor_get(v___x_1357_, 1);
v_zetaDeltaFVarIds_1359_ = lean_ctor_get(v___x_1357_, 2);
v_postponed_1360_ = lean_ctor_get(v___x_1357_, 3);
v_diag_1361_ = lean_ctor_get(v___x_1357_, 4);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1357_, 0);
lean_dec(v_unused_1372_);
v___x_1363_ = v___x_1357_;
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_diag_1361_);
lean_inc(v_postponed_1360_);
lean_inc(v_zetaDeltaFVarIds_1359_);
lean_inc(v_cache_1358_);
lean_dec(v___x_1357_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v_mctx_1356_);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_mctx_1356_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_cache_1358_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_zetaDeltaFVarIds_1359_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_postponed_1360_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_diag_1361_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = lean_st_ref_set(v___y_1266_, v___x_1366_);
v___x_1368_ = lean_box(v_fst_1355_);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
v___jp_1373_:
{
lean_object* v_snd_1375_; lean_object* v_fst_1376_; lean_object* v_mctx_1377_; uint8_t v___x_1378_; 
v_snd_1375_ = lean_ctor_get(v___y_1374_, 1);
lean_inc(v_snd_1375_);
v_fst_1376_ = lean_ctor_get(v___y_1374_, 0);
lean_inc(v_fst_1376_);
lean_dec_ref(v___y_1374_);
v_mctx_1377_ = lean_ctor_get(v_snd_1375_, 1);
lean_inc_ref(v_mctx_1377_);
lean_dec(v_snd_1375_);
v___x_1378_ = lean_unbox(v_fst_1376_);
lean_dec(v_fst_1376_);
v_fst_1355_ = v___x_1378_;
v_mctx_1356_ = v_mctx_1377_;
goto v___jp_1354_;
}
}
}
v___jp_1332_:
{
if (v_fst_1333_ == 0)
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_Expr_hasFVar(v_value_1330_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Lean_Expr_hasMVar(v_value_1330_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v_value_1330_);
lean_dec_ref(v___f_1293_);
v_fst_1269_ = v___x_1336_;
v_snd_1270_ = v_snd_1334_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_value_1330_, v_snd_1334_);
v___y_1289_ = v___x_1337_;
goto v___jp_1288_;
}
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_value_1330_, v_snd_1334_);
v___y_1289_ = v___x_1338_;
goto v___jp_1288_;
}
}
else
{
lean_dec_ref(v_value_1330_);
lean_dec_ref(v___f_1293_);
v_fst_1269_ = v_fst_1333_;
v_snd_1270_ = v_snd_1334_;
goto v___jp_1268_;
}
}
v___jp_1339_:
{
lean_object* v_fst_1341_; lean_object* v_snd_1342_; uint8_t v___x_1343_; 
v_fst_1341_ = lean_ctor_get(v___y_1340_, 0);
lean_inc(v_fst_1341_);
v_snd_1342_ = lean_ctor_get(v___y_1340_, 1);
lean_inc(v_snd_1342_);
lean_dec_ref(v___y_1340_);
v___x_1343_ = lean_unbox(v_fst_1341_);
lean_dec(v_fst_1341_);
v_fst_1333_ = v___x_1343_;
v_snd_1334_ = v_snd_1342_;
goto v___jp_1332_;
}
v___jp_1344_:
{
lean_object* v___x_1345_; lean_object* v_mctx_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1345_ = lean_st_ref_get(v___y_1266_);
v_mctx_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_ref(v_mctx_1346_);
lean_dec(v___x_1345_);
v___x_1347_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_mctx_1346_);
v___x_1349_ = l_Lean_Expr_hasFVar(v_type_1329_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Lean_Expr_hasMVar(v_type_1329_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v_type_1329_);
v_fst_1333_ = v___x_1350_;
v_snd_1334_ = v___x_1348_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1351_; 
lean_inc_ref(v___f_1293_);
v___x_1351_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_type_1329_, v___x_1348_);
v___y_1340_ = v___x_1351_;
goto v___jp_1339_;
}
}
else
{
lean_object* v___x_1352_; 
lean_inc_ref(v___f_1293_);
v___x_1352_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1293_, v___f_1294_, v_type_1329_, v___x_1348_);
v___y_1340_ = v___x_1352_;
goto v___jp_1339_;
}
}
}
v___jp_1268_:
{
lean_object* v_mctx_1271_; lean_object* v___x_1272_; lean_object* v_cache_1273_; lean_object* v_zetaDeltaFVarIds_1274_; lean_object* v_postponed_1275_; lean_object* v_diag_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1286_; 
v_mctx_1271_ = lean_ctor_get(v_snd_1270_, 1);
lean_inc_ref(v_mctx_1271_);
lean_dec_ref(v_snd_1270_);
v___x_1272_ = lean_st_ref_take(v___y_1266_);
v_cache_1273_ = lean_ctor_get(v___x_1272_, 1);
v_zetaDeltaFVarIds_1274_ = lean_ctor_get(v___x_1272_, 2);
v_postponed_1275_ = lean_ctor_get(v___x_1272_, 3);
v_diag_1276_ = lean_ctor_get(v___x_1272_, 4);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1272_, 0);
lean_dec(v_unused_1287_);
v___x_1278_ = v___x_1272_;
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_diag_1276_);
lean_inc(v_postponed_1275_);
lean_inc(v_zetaDeltaFVarIds_1274_);
lean_inc(v_cache_1273_);
lean_dec(v___x_1272_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v_mctx_1271_);
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_mctx_1271_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_cache_1273_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_zetaDeltaFVarIds_1274_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_postponed_1275_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_diag_1276_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_st_ref_set(v___y_1266_, v___x_1281_);
v___x_1283_ = lean_box(v_fst_1269_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
}
v___jp_1288_:
{
lean_object* v_fst_1290_; lean_object* v_snd_1291_; uint8_t v___x_1292_; 
v_fst_1290_ = lean_ctor_get(v___y_1289_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v___y_1289_, 1);
lean_inc(v_snd_1291_);
lean_dec_ref(v___y_1289_);
v___x_1292_ = lean_unbox(v_fst_1290_);
lean_dec(v_fst_1290_);
v_fst_1269_ = v___x_1292_;
v_snd_1270_ = v_snd_1291_;
goto v___jp_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1386_, lean_object* v_fvarId_1387_, lean_object* v_generalizeNondepLet_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1391_; lean_object* v_res_1392_; 
v_generalizeNondepLet_boxed_1391_ = lean_unbox(v_generalizeNondepLet_1388_);
v_res_1392_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1386_, v_fvarId_1387_, v_generalizeNondepLet_boxed_1391_, v___y_1389_);
lean_dec(v___y_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1393_, lean_object* v_fvarId_1394_, uint8_t v_generalizeNondepLet_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1393_, v_fvarId_1394_, v_generalizeNondepLet_1395_, v___y_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1402_, lean_object* v_fvarId_1403_, lean_object* v_generalizeNondepLet_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1410_; lean_object* v_res_1411_; 
v_generalizeNondepLet_boxed_1410_ = lean_unbox(v_generalizeNondepLet_1404_);
v_res_1411_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1402_, v_fvarId_1403_, v_generalizeNondepLet_boxed_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1412_, lean_object* v_fvarId_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; uint8_t v_fst_1418_; lean_object* v_mctx_1419_; lean_object* v___y_1437_; lean_object* v_mctx_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1416_ = lean_st_ref_get(v___y_1414_);
v_mctx_1442_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_mctx_1442_);
lean_dec(v___x_1416_);
v___f_1443_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1444_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1444_, 0, v_fvarId_1413_);
v___x_1445_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_1442_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v_mctx_1442_);
v___x_1447_ = l_Lean_Expr_hasFVar(v_e_1412_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
v___x_1448_ = l_Lean_Expr_hasMVar(v_e_1412_);
if (v___x_1448_ == 0)
{
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___f_1444_);
lean_dec_ref(v_e_1412_);
v_fst_1418_ = v___x_1448_;
v_mctx_1419_ = v_mctx_1442_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1449_; 
lean_dec_ref(v_mctx_1442_);
v___x_1449_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1444_, v___f_1443_, v_e_1412_, v___x_1446_);
v___y_1437_ = v___x_1449_;
goto v___jp_1436_;
}
}
else
{
lean_object* v___x_1450_; 
lean_dec_ref(v_mctx_1442_);
v___x_1450_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1444_, v___f_1443_, v_e_1412_, v___x_1446_);
v___y_1437_ = v___x_1450_;
goto v___jp_1436_;
}
v___jp_1417_:
{
lean_object* v___x_1420_; lean_object* v_cache_1421_; lean_object* v_zetaDeltaFVarIds_1422_; lean_object* v_postponed_1423_; lean_object* v_diag_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1434_; 
v___x_1420_ = lean_st_ref_take(v___y_1414_);
v_cache_1421_ = lean_ctor_get(v___x_1420_, 1);
v_zetaDeltaFVarIds_1422_ = lean_ctor_get(v___x_1420_, 2);
v_postponed_1423_ = lean_ctor_get(v___x_1420_, 3);
v_diag_1424_ = lean_ctor_get(v___x_1420_, 4);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1435_);
v___x_1426_ = v___x_1420_;
v_isShared_1427_ = v_isSharedCheck_1434_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_diag_1424_);
lean_inc(v_postponed_1423_);
lean_inc(v_zetaDeltaFVarIds_1422_);
lean_inc(v_cache_1421_);
lean_dec(v___x_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1434_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v_mctx_1419_);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_mctx_1419_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_cache_1421_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_zetaDeltaFVarIds_1422_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v_postponed_1423_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_diag_1424_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_st_ref_set(v___y_1414_, v___x_1429_);
v___x_1431_ = lean_box(v_fst_1418_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
}
v___jp_1436_:
{
lean_object* v_snd_1438_; lean_object* v_fst_1439_; lean_object* v_mctx_1440_; uint8_t v___x_1441_; 
v_snd_1438_ = lean_ctor_get(v___y_1437_, 1);
lean_inc(v_snd_1438_);
v_fst_1439_ = lean_ctor_get(v___y_1437_, 0);
lean_inc(v_fst_1439_);
lean_dec_ref(v___y_1437_);
v_mctx_1440_ = lean_ctor_get(v_snd_1438_, 1);
lean_inc_ref(v_mctx_1440_);
lean_dec(v_snd_1438_);
v___x_1441_ = lean_unbox(v_fst_1439_);
lean_dec(v_fst_1439_);
v_fst_1418_ = v___x_1441_;
v_mctx_1419_ = v_mctx_1440_;
goto v___jp_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1451_, lean_object* v_fvarId_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1451_, v_fvarId_1452_, v___y_1453_);
lean_dec(v___y_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1456_, lean_object* v_fvarId_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1456_, v_fvarId_1457_, v___y_1459_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1464_, lean_object* v_fvarId_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1464_, v_fvarId_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1471_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1472_, lean_object* v_x_1473_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
else
{
lean_object* v_head_1475_; lean_object* v_tail_1476_; uint8_t v___x_1477_; 
v_head_1475_ = lean_ctor_get(v_x_1473_, 0);
v_tail_1476_ = lean_ctor_get(v_x_1473_, 1);
v___x_1477_ = lean_nat_dec_eq(v_a_1472_, v_head_1475_);
if (v___x_1477_ == 0)
{
v_x_1473_ = v_tail_1476_;
goto _start;
}
else
{
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1479_, lean_object* v_x_1480_){
_start:
{
uint8_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1479_, v_x_1480_);
lean_dec(v_x_1480_);
lean_dec(v_a_1479_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1495_, lean_object* v_idx_1496_, lean_object* v_tacticName_1497_, lean_object* v_mvarId_1498_, lean_object* v_idxPos_1499_, lean_object* v_recursorInfo_1500_, lean_object* v_majorType_1501_, lean_object* v_n_1502_, lean_object* v_i_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_zero_1509_; uint8_t v_isZero_1510_; 
v_zero_1509_ = lean_unsigned_to_nat(0u);
v_isZero_1510_ = lean_nat_dec_eq(v_i_1503_, v_zero_1509_);
if (v_isZero_1510_ == 1)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec_ref(v___y_1504_);
lean_dec(v_i_1503_);
lean_dec_ref(v_majorType_1501_);
lean_dec(v_mvarId_1498_);
lean_dec(v_tacticName_1497_);
lean_dec_ref(v_idx_1496_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
else
{
lean_object* v_one_1513_; lean_object* v_n_1514_; lean_object* v___y_1516_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_arg_1520_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; uint8_t v___y_1526_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; uint8_t v___x_1597_; 
v_one_1513_ = lean_unsigned_to_nat(1u);
v_n_1514_ = lean_nat_sub(v_i_1503_, v_one_1513_);
lean_dec(v_i_1503_);
v___x_1518_ = lean_nat_sub(v_n_1502_, v_n_1514_);
v___x_1519_ = lean_nat_sub(v___x_1518_, v_one_1513_);
lean_dec(v___x_1518_);
v_arg_1520_ = lean_array_fget_borrowed(v_majorTypeArgs_1495_, v___x_1519_);
v___x_1597_ = lean_nat_dec_eq(v___x_1519_, v_idxPos_1499_);
if (v___x_1597_ == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_expr_eqv(v_arg_1520_, v_idx_1496_);
if (v___x_1598_ == 0)
{
lean_inc_ref(v___y_1504_);
v___y_1573_ = v___y_1504_;
v___y_1574_ = v___y_1505_;
v___y_1575_ = v___y_1506_;
v___y_1576_ = v___y_1507_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1599_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1496_);
v___x_1600_ = l_Lean_MessageData_ofExpr(v_idx_1496_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
lean_inc_ref(v_majorType_1501_);
v___x_1604_ = l_Lean_indentExpr(v_majorType_1501_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_inc(v_mvarId_1498_);
lean_inc(v_tacticName_1497_);
v___x_1607_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1497_, v_mvarId_1498_, v___x_1606_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref(v___x_1607_);
lean_inc_ref(v___y_1504_);
v___y_1573_ = v___y_1504_;
v___y_1574_ = v___y_1505_;
v___y_1575_ = v___y_1506_;
v___y_1576_ = v___y_1507_;
goto v___jp_1572_;
}
else
{
lean_dec(v___x_1519_);
v___y_1516_ = v___x_1607_;
goto v___jp_1515_;
}
}
}
else
{
lean_inc_ref(v___y_1504_);
v___y_1573_ = v___y_1504_;
v___y_1574_ = v___y_1505_;
v___y_1575_ = v___y_1506_;
v___y_1576_ = v___y_1507_;
goto v___jp_1572_;
}
v___jp_1515_:
{
if (lean_obj_tag(v___y_1516_) == 0)
{
lean_dec_ref(v___y_1516_);
v_i_1503_ = v_n_1514_;
goto _start;
}
else
{
lean_dec(v_n_1514_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_majorType_1501_);
lean_dec(v_mvarId_1498_);
lean_dec(v_tacticName_1497_);
lean_dec_ref(v_idx_1496_);
return v___y_1516_;
}
}
v___jp_1521_:
{
if (v___y_1526_ == 0)
{
lean_dec_ref(v___y_1524_);
lean_dec(v___x_1519_);
v_i_1503_ = v_n_1514_;
goto _start;
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = l_Lean_Expr_isFVar(v_arg_1520_);
if (v___x_1528_ == 0)
{
lean_dec_ref(v___y_1524_);
lean_dec(v___x_1519_);
v_i_1503_ = v_n_1514_;
goto _start;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = l_Lean_Expr_fvarId_x21(v_idx_1496_);
lean_inc_ref(v___y_1524_);
v___x_1531_ = l_Lean_FVarId_getDecl___redArg(v___x_1530_, v___y_1524_, v___y_1525_, v___y_1523_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1555_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1531_);
v___x_1533_ = l_Lean_Expr_fvarId_x21(v_arg_1520_);
v___x_1534_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1532_, v___x_1533_, v___y_1526_, v___y_1522_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1555_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1555_;
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
lean_dec_ref(v___y_1524_);
lean_dec(v___x_1519_);
v_i_1503_ = v_n_1514_;
goto _start;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1541_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1496_);
v___x_1542_ = l_Lean_MessageData_ofExpr(v_idx_1496_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_nat_add(v___x_1519_, v_one_1513_);
lean_dec(v___x_1519_);
v___x_1547_ = l_Nat_reprFast(v___x_1546_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 3);
lean_ctor_set(v___x_1537_, 0, v___x_1547_);
v___x_1549_ = v___x_1537_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1550_ = l_Lean_MessageData_ofFormat(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1545_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_inc(v_mvarId_1498_);
lean_inc(v_tacticName_1497_);
v___x_1553_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1497_, v_mvarId_1498_, v___x_1552_, v___y_1524_, v___y_1522_, v___y_1525_, v___y_1523_);
lean_dec_ref(v___y_1524_);
v___y_1516_ = v___x_1553_;
goto v___jp_1515_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v___y_1524_);
lean_dec(v___x_1519_);
lean_dec(v_n_1514_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_majorType_1501_);
lean_dec(v_mvarId_1498_);
lean_dec(v_tacticName_1497_);
lean_dec_ref(v_idx_1496_);
v_a_1556_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1531_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1531_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
v___jp_1564_:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_lt(v_idxPos_1499_, v___x_1519_);
if (v___x_1569_ == 0)
{
v___y_1522_ = v___y_1566_;
v___y_1523_ = v___y_1568_;
v___y_1524_ = v___y_1565_;
v___y_1525_ = v___y_1567_;
v___y_1526_ = v___x_1569_;
goto v___jp_1521_;
}
else
{
lean_object* v_indicesPos_1570_; uint8_t v___x_1571_; 
v_indicesPos_1570_ = lean_ctor_get(v_recursorInfo_1500_, 6);
v___x_1571_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1519_, v_indicesPos_1570_);
v___y_1522_ = v___y_1566_;
v___y_1523_ = v___y_1568_;
v___y_1524_ = v___y_1565_;
v___y_1525_ = v___y_1567_;
v___y_1526_ = v___x_1571_;
goto v___jp_1521_;
}
}
v___jp_1572_:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_lt(v___x_1519_, v_idxPos_1499_);
if (v___x_1577_ == 0)
{
v___y_1565_ = v___y_1573_;
v___y_1566_ = v___y_1574_;
v___y_1567_ = v___y_1575_;
v___y_1568_ = v___y_1576_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1596_; 
v___x_1578_ = l_Lean_Expr_fvarId_x21(v_idx_1496_);
lean_inc(v_arg_1520_);
v___x_1579_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1520_, v___x_1578_, v___y_1574_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1596_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1596_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
if (v___x_1584_ == 0)
{
lean_del_object(v___x_1582_);
v___y_1565_ = v___y_1573_;
v___y_1566_ = v___y_1574_;
v___y_1567_ = v___y_1575_;
v___y_1568_ = v___y_1576_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1585_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1496_);
v___x_1586_ = l_Lean_MessageData_ofExpr(v_idx_1496_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
lean_inc_ref(v_majorType_1501_);
v___x_1590_ = l_Lean_indentExpr(v_majorType_1501_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1591_);
v___x_1593_ = v___x_1582_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
lean_inc(v_mvarId_1498_);
lean_inc(v_tacticName_1497_);
v___x_1594_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1497_, v_mvarId_1498_, v___x_1593_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_dec_ref(v___x_1594_);
v___y_1565_ = v___y_1573_;
v___y_1566_ = v___y_1574_;
v___y_1567_ = v___y_1575_;
v___y_1568_ = v___y_1576_;
goto v___jp_1564_;
}
else
{
lean_dec_ref(v___y_1573_);
lean_dec(v___x_1519_);
v___y_1516_ = v___x_1594_;
goto v___jp_1515_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1608_, lean_object* v_idx_1609_, lean_object* v_tacticName_1610_, lean_object* v_mvarId_1611_, lean_object* v_idxPos_1612_, lean_object* v_recursorInfo_1613_, lean_object* v_majorType_1614_, lean_object* v_n_1615_, lean_object* v_i_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1608_, v_idx_1609_, v_tacticName_1610_, v_mvarId_1611_, v_idxPos_1612_, v_recursorInfo_1613_, v_majorType_1614_, v_n_1615_, v_i_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec(v_n_1615_);
lean_dec_ref(v_recursorInfo_1613_);
lean_dec(v_idxPos_1612_);
lean_dec_ref(v_majorTypeArgs_1608_);
return v_res_1622_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1625_ = l_Lean_stringToMessageData(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1628_ = l_Lean_stringToMessageData(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1632_, lean_object* v_tacticName_1633_, lean_object* v_mvarId_1634_, lean_object* v_recursorInfo_1635_, lean_object* v_majorType_1636_, size_t v_sz_1637_, size_t v_i_1638_, lean_object* v_bs_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_lt(v_i_1638_, v_sz_1637_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_majorType_1636_);
lean_dec(v_mvarId_1634_);
lean_dec(v_tacticName_1633_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_bs_1639_);
return v___x_1646_;
}
else
{
lean_object* v_v_1647_; lean_object* v___x_1648_; lean_object* v_bs_x27_1649_; lean_object* v_a_1651_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_v_1647_ = lean_array_uget(v_bs_1639_, v_i_1638_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v_bs_x27_1649_ = lean_array_uset(v_bs_1639_, v_i_1638_, v___x_1648_);
v___x_1656_ = lean_array_get_size(v_majorTypeArgs_1632_);
v___x_1657_ = lean_nat_dec_le(v___x_1656_, v_v_1647_);
if (v___x_1657_ == 0)
{
lean_object* v_idx_1658_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; uint8_t v___x_1673_; 
v_idx_1658_ = lean_array_fget_borrowed(v_majorTypeArgs_1632_, v_v_1647_);
v___x_1673_ = l_Lean_Expr_isFVar(v_idx_1658_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1658_);
v___x_1675_ = l_Lean_MessageData_ofExpr(v_idx_1658_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
lean_inc_ref(v_majorType_1636_);
v___x_1679_ = l_Lean_indentExpr(v_majorType_1636_);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_inc(v_mvarId_1634_);
lean_inc(v_tacticName_1633_);
v___x_1682_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1633_, v_mvarId_1634_, v___x_1681_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_dec_ref(v___x_1682_);
lean_inc_ref(v___y_1640_);
v___y_1660_ = v___y_1640_;
v___y_1661_ = v___y_1641_;
v___y_1662_ = v___y_1642_;
v___y_1663_ = v___y_1643_;
goto v___jp_1659_;
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_bs_x27_1649_);
lean_dec(v_v_1647_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_majorType_1636_);
lean_dec(v_mvarId_1634_);
lean_dec(v_tacticName_1633_);
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_inc_ref(v___y_1640_);
v___y_1660_ = v___y_1640_;
v___y_1661_ = v___y_1641_;
v___y_1662_ = v___y_1642_;
v___y_1663_ = v___y_1643_;
goto v___jp_1659_;
}
v___jp_1659_:
{
lean_object* v___x_1664_; 
lean_inc_ref(v_majorType_1636_);
lean_inc(v_mvarId_1634_);
lean_inc(v_tacticName_1633_);
lean_inc(v_idx_1658_);
v___x_1664_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1632_, v_idx_1658_, v_tacticName_1633_, v_mvarId_1634_, v_v_1647_, v_recursorInfo_1635_, v_majorType_1636_, v___x_1656_, v___x_1656_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v_v_1647_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_dec_ref(v___x_1664_);
lean_inc(v_idx_1658_);
v_a_1651_ = v_idx_1658_;
goto v___jp_1650_;
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v_bs_x27_1649_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_majorType_1636_);
lean_dec(v_mvarId_1634_);
lean_dec(v_tacticName_1633_);
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_v_1647_);
v___x_1691_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1636_);
v___x_1692_ = l_Lean_indentExpr(v_majorType_1636_);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_inc(v_mvarId_1634_);
lean_inc(v_tacticName_1633_);
v___x_1695_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1633_, v_mvarId_1634_, v___x_1694_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v_a_1651_ = v_a_1696_;
goto v___jp_1650_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_bs_x27_1649_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_majorType_1636_);
lean_dec(v_mvarId_1634_);
lean_dec(v_tacticName_1633_);
v_a_1697_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1695_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
v___jp_1650_:
{
size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_add(v_i_1638_, v___x_1652_);
v___x_1654_ = lean_array_uset(v_bs_x27_1649_, v_i_1638_, v_a_1651_);
v_i_1638_ = v___x_1653_;
v_bs_1639_ = v___x_1654_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1705_, lean_object* v_tacticName_1706_, lean_object* v_mvarId_1707_, lean_object* v_recursorInfo_1708_, lean_object* v_majorType_1709_, lean_object* v_sz_1710_, lean_object* v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1710_);
lean_dec(v_sz_1710_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1705_, v_tacticName_1706_, v_mvarId_1707_, v_recursorInfo_1708_, v_majorType_1709_, v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v_recursorInfo_1708_);
lean_dec_ref(v_majorTypeArgs_1705_);
return v_res_1720_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1721_; lean_object* v_dummy_1722_; 
v___x_1721_ = lean_box(0);
v_dummy_1722_ = l_Lean_Expr_sort___override(v___x_1721_);
return v_dummy_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1723_, lean_object* v_tacticName_1724_, lean_object* v_recursorInfo_1725_, lean_object* v_majorType_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_indicesPos_1732_; lean_object* v_nargs_1733_; lean_object* v_dummy_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_majorTypeArgs_1738_; lean_object* v___x_1739_; size_t v_sz_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v_indicesPos_1732_ = lean_ctor_get(v_recursorInfo_1725_, 6);
v_nargs_1733_ = l_Lean_Expr_getAppNumArgs(v_majorType_1726_);
v_dummy_1734_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1733_);
v___x_1735_ = lean_mk_array(v_nargs_1733_, v_dummy_1734_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_sub(v_nargs_1733_, v___x_1736_);
lean_dec(v_nargs_1733_);
lean_inc_ref(v_majorType_1726_);
v_majorTypeArgs_1738_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1726_, v___x_1735_, v___x_1737_);
lean_inc(v_indicesPos_1732_);
v___x_1739_ = lean_array_mk(v_indicesPos_1732_);
v_sz_1740_ = lean_array_size(v___x_1739_);
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1738_, v_tacticName_1724_, v_mvarId_1723_, v_recursorInfo_1725_, v_majorType_1726_, v_sz_1740_, v___x_1741_, v___x_1739_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec_ref(v_recursorInfo_1725_);
lean_dec_ref(v_majorTypeArgs_1738_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1743_, lean_object* v_tacticName_1744_, lean_object* v_recursorInfo_1745_, lean_object* v_majorType_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1743_, v_tacticName_1744_, v_recursorInfo_1745_, v_majorType_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1753_, lean_object* v_idx_1754_, lean_object* v_tacticName_1755_, lean_object* v_mvarId_1756_, lean_object* v_idxPos_1757_, lean_object* v_recursorInfo_1758_, lean_object* v_majorType_1759_, lean_object* v_n_1760_, lean_object* v_i_1761_, lean_object* v_a_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1753_, v_idx_1754_, v_tacticName_1755_, v_mvarId_1756_, v_idxPos_1757_, v_recursorInfo_1758_, v_majorType_1759_, v_n_1760_, v_i_1761_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1769_, lean_object* v_idx_1770_, lean_object* v_tacticName_1771_, lean_object* v_mvarId_1772_, lean_object* v_idxPos_1773_, lean_object* v_recursorInfo_1774_, lean_object* v_majorType_1775_, lean_object* v_n_1776_, lean_object* v_i_1777_, lean_object* v_a_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1769_, v_idx_1770_, v_tacticName_1771_, v_mvarId_1772_, v_idxPos_1773_, v_recursorInfo_1774_, v_majorType_1775_, v_n_1776_, v_i_1777_, v_a_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec(v_n_1776_);
lean_dec_ref(v_recursorInfo_1774_);
lean_dec(v_idxPos_1773_);
lean_dec_ref(v_majorTypeArgs_1769_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_ref_1792_; lean_object* v_msg_1793_; lean_object* v___x_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1803_; 
v_ref_1792_ = lean_ctor_get(v___y_1789_, 5);
v_msg_1793_ = l_Lean_MessageData_tagWithErrorName(v_msg_1786_, v_name_1785_);
v___x_1794_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2_spec__3(v_msg_1793_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_inc(v_ref_1792_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_ref_1792_);
lean_ctor_set(v___x_1799_, 1, v_a_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
lean_ctor_set(v___x_1797_, 0, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1804_, lean_object* v_msg_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1804_, v_msg_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1812_, lean_object* v___x_1813_, lean_object* v_tacticName_1814_, lean_object* v_mvarId_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
if (lean_obj_tag(v_x_1817_) == 0)
{
lean_object* v___x_1823_; 
lean_dec(v_mvarId_1815_);
lean_dec(v_tacticName_1814_);
lean_dec(v_a_1812_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_x_1816_);
return v___x_1823_;
}
else
{
lean_object* v_head_1824_; 
v_head_1824_ = lean_ctor_get(v_x_1817_, 0);
if (lean_obj_tag(v_head_1824_) == 0)
{
lean_object* v_tail_1825_; lean_object* v_fst_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1837_; 
v_tail_1825_ = lean_ctor_get(v_x_1817_, 1);
v_fst_1826_ = lean_ctor_get(v_x_1816_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_x_1816_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_x_1816_, 1);
lean_dec(v_unused_1838_);
v___x_1828_ = v_x_1816_;
v_isShared_1829_ = v_isSharedCheck_1837_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_fst_1826_);
lean_dec(v_x_1816_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1837_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_inc(v_a_1812_);
v___x_1830_ = lean_array_push(v_fst_1826_, v_a_1812_);
v___x_1831_ = 1;
v___x_1832_ = lean_box(v___x_1831_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___x_1832_);
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1834_ = v___x_1828_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v_x_1816_ = v___x_1834_;
v_x_1817_ = v_tail_1825_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1858_; 
v_tail_1839_ = lean_ctor_get(v_x_1817_, 1);
v_fst_1840_ = lean_ctor_get(v_x_1816_, 0);
v_snd_1841_ = lean_ctor_get(v_x_1816_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_x_1816_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1843_ = v_x_1816_;
v_isShared_1844_ = v_isSharedCheck_1858_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snd_1841_);
lean_inc(v_fst_1840_);
lean_dec(v_x_1816_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1858_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_idx_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v_idx_1845_ = lean_ctor_get(v_head_1824_, 0);
v___x_1846_ = lean_array_get_size(v___x_1813_);
v___x_1847_ = lean_nat_dec_le(v___x_1846_, v_idx_1845_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1848_ = lean_array_fget_borrowed(v___x_1813_, v_idx_1845_);
lean_inc(v___x_1848_);
v___x_1849_ = lean_array_push(v_fst_1840_, v___x_1848_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1849_);
v___x_1851_ = v___x_1843_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_snd_1841_);
v___x_1851_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
v_x_1816_ = v___x_1851_;
v_x_1817_ = v_tail_1839_;
goto _start;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_del_object(v___x_1843_);
lean_dec(v_snd_1841_);
lean_dec(v_fst_1840_);
v___x_1854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1815_);
lean_inc(v_tacticName_1814_);
v___x_1855_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1814_, v_mvarId_1815_, v___x_1854_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1855_);
v_x_1816_ = v_a_1856_;
v_x_1817_ = v_tail_1839_;
goto _start;
}
else
{
lean_dec(v_mvarId_1815_);
lean_dec(v_tacticName_1814_);
lean_dec(v_a_1812_);
return v___x_1855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1859_, lean_object* v___x_1860_, lean_object* v_tacticName_1861_, lean_object* v_mvarId_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1859_, v___x_1860_, v_tacticName_1861_, v_mvarId_1862_, v_x_1863_, v_x_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_x_1864_);
lean_dec_ref(v___x_1860_);
return v_res_1870_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1890_ = l_Lean_stringToMessageData(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1895_ = l_Lean_MessageData_ofFormat(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1898_, lean_object* v_a_1899_, lean_object* v_tacticName_1900_, lean_object* v_mvarId_1901_, lean_object* v_indices_1902_, lean_object* v_a_1903_, lean_object* v_major_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
if (lean_obj_tag(v_x_1905_) == 5)
{
lean_object* v_fn_1913_; lean_object* v_arg_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_fn_1913_ = lean_ctor_get(v_x_1905_, 0);
lean_inc_ref(v_fn_1913_);
v_arg_1914_ = lean_ctor_get(v_x_1905_, 1);
lean_inc_ref(v_arg_1914_);
lean_dec_ref(v_x_1905_);
v___x_1915_ = lean_array_set(v_x_1906_, v_x_1907_, v_arg_1914_);
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_sub(v_x_1907_, v___x_1916_);
lean_dec(v_x_1907_);
v_x_1905_ = v_fn_1913_;
v_x_1906_ = v___x_1915_;
v_x_1907_ = v___x_1917_;
goto _start;
}
else
{
lean_dec(v_x_1907_);
if (lean_obj_tag(v_x_1905_) == 4)
{
lean_object* v_us_1919_; lean_object* v_recursorName_1920_; lean_object* v_univLevelPos_1921_; uint8_t v_depElim_1922_; lean_object* v_paramsPos_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; lean_object* v___y_1927_; lean_object* v_motive_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_us_1919_ = lean_ctor_get(v_x_1905_, 1);
lean_inc(v_us_1919_);
lean_dec_ref(v_x_1905_);
v_recursorName_1920_ = lean_ctor_get(v_recursorInfo_1898_, 0);
lean_inc(v_recursorName_1920_);
v_univLevelPos_1921_ = lean_ctor_get(v_recursorInfo_1898_, 2);
lean_inc(v_univLevelPos_1921_);
v_depElim_1922_ = lean_ctor_get_uint8(v_recursorInfo_1898_, sizeof(void*)*8);
v_paramsPos_1923_ = lean_ctor_get(v_recursorInfo_1898_, 5);
lean_inc(v_paramsPos_1923_);
lean_dec_ref(v_recursorInfo_1898_);
v___x_1924_ = lean_array_mk(v_us_1919_);
v___x_1925_ = 0;
v___x_1945_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1901_);
lean_inc(v_tacticName_1900_);
lean_inc(v_a_1899_);
v___x_1946_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1899_, v___x_1924_, v_tacticName_1900_, v_mvarId_1901_, v___x_1945_, v_univLevelPos_1921_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v_univLevelPos_1921_);
lean_dec_ref(v___x_1924_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1993_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v_fst_1948_ = lean_ctor_get(v_a_1947_, 0);
v_snd_1949_ = lean_ctor_get(v_a_1947_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1951_ = v_a_1947_;
v_isShared_1952_ = v_isSharedCheck_1993_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_inc(v_fst_1948_);
lean_dec(v_a_1947_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1993_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; uint8_t v___x_1973_; 
v___x_1973_ = lean_unbox(v_snd_1949_);
lean_dec(v_snd_1949_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; 
v___x_1974_ = l_Lean_Level_isZero(v_a_1899_);
lean_dec(v_a_1899_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
lean_dec(v_fst_1948_);
lean_dec(v_paramsPos_1923_);
lean_dec_ref(v_x_1906_);
lean_dec_ref(v_major_1904_);
lean_dec_ref(v_a_1903_);
v___x_1975_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1976_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1977_ = l_Lean_MessageData_ofName(v_recursorName_1920_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 7);
lean_ctor_set(v___x_1951_, 1, v___x_1977_);
lean_ctor_set(v___x_1951_, 0, v___x_1976_);
v___x_1979_ = v___x_1951_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v___x_1980_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1900_, v_mvarId_1901_, v___x_1981_);
v___x_1983_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1975_, v___x_1982_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_del_object(v___x_1951_);
lean_dec(v_tacticName_1900_);
v___y_1954_ = v___y_1908_;
v___y_1955_ = v___y_1909_;
v___y_1956_ = v___y_1910_;
v___y_1957_ = v___y_1911_;
goto v___jp_1953_;
}
}
else
{
lean_del_object(v___x_1951_);
lean_dec(v_tacticName_1900_);
lean_dec(v_a_1899_);
v___y_1954_ = v___y_1908_;
v___y_1955_ = v___y_1909_;
v___y_1956_ = v___y_1910_;
v___y_1957_ = v___y_1911_;
goto v___jp_1953_;
}
v___jp_1953_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_array_to_list(v_fst_1948_);
v___x_1959_ = l_Lean_mkConst(v_recursorName_1920_, v___x_1958_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
v___x_1960_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1901_, v_x_1906_, v_paramsPos_1923_, v___x_1959_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec_ref(v_x_1906_);
if (lean_obj_tag(v___x_1960_) == 0)
{
if (v_depElim_1922_ == 0)
{
lean_object* v_a_1961_; 
lean_dec_ref(v_major_1904_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___x_1960_);
v___y_1927_ = v_a_1961_;
v_motive_1928_ = v_a_1903_;
v___y_1929_ = v___y_1954_;
v___y_1930_ = v___y_1955_;
v___y_1931_ = v___y_1956_;
v___y_1932_ = v___y_1957_;
goto v___jp_1926_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1963_; 
v_a_1962_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1960_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc_ref(v_major_1904_);
v___x_1963_ = lean_infer_type(v_major_1904_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_mk_empty_array_with_capacity(v___x_1965_);
v___x_1967_ = lean_array_push(v___x_1966_, v_major_1904_);
v___x_1968_ = l_Lean_Expr_abstractM(v_a_1903_, v___x_1967_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec_ref(v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1971_ = 0;
v___x_1972_ = l_Lean_mkLambda(v___x_1970_, v___x_1971_, v_a_1964_, v_a_1969_);
v___y_1927_ = v_a_1962_;
v_motive_1928_ = v___x_1972_;
v___y_1929_ = v___y_1954_;
v___y_1930_ = v___y_1955_;
v___y_1931_ = v___y_1956_;
v___y_1932_ = v___y_1957_;
goto v___jp_1926_;
}
else
{
lean_dec(v_a_1964_);
lean_dec(v_a_1962_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v___x_1968_;
}
}
else
{
lean_dec(v_a_1962_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_major_1904_);
lean_dec_ref(v_a_1903_);
return v___x_1963_;
}
}
}
else
{
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_major_1904_);
lean_dec_ref(v_a_1903_);
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_paramsPos_1923_);
lean_dec(v_recursorName_1920_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec_ref(v_x_1906_);
lean_dec_ref(v_major_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_mvarId_1901_);
lean_dec(v_tacticName_1900_);
lean_dec(v_a_1899_);
v_a_1994_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1946_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1946_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
v___jp_1926_:
{
uint8_t v___x_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = 1;
v___x_1934_ = 1;
v___x_1935_ = l_Lean_Meta_mkLambdaFVars(v_indices_1902_, v_motive_1928_, v___x_1925_, v___x_1933_, v___x_1925_, v___x_1933_, v___x_1934_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_Expr_app___override(v___y_1927_, v_a_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_dec_ref(v___y_1927_);
return v___x_1935_;
}
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec_ref(v_x_1906_);
lean_dec_ref(v_x_1905_);
lean_dec_ref(v_major_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1899_);
lean_dec_ref(v_recursorInfo_1898_);
v___x_2002_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2003_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1900_, v_mvarId_1901_, v___x_2002_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_2004_, lean_object* v_a_2005_, lean_object* v_tacticName_2006_, lean_object* v_mvarId_2007_, lean_object* v_indices_2008_, lean_object* v_a_2009_, lean_object* v_major_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_2004_, v_a_2005_, v_tacticName_2006_, v_mvarId_2007_, v_indices_2008_, v_a_2009_, v_major_2010_, v_x_2011_, v_x_2012_, v_x_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec_ref(v_indices_2008_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_2020_, lean_object* v_tacticName_2021_, lean_object* v_mvarId_2022_, lean_object* v_recursorInfo_2023_, lean_object* v_indices_2024_, lean_object* v_a_2025_, lean_object* v_major_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 5)
{
lean_object* v_fn_2035_; lean_object* v_arg_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_fn_2035_ = lean_ctor_get(v_x_2027_, 0);
lean_inc_ref(v_fn_2035_);
v_arg_2036_ = lean_ctor_get(v_x_2027_, 1);
lean_inc_ref(v_arg_2036_);
lean_dec_ref(v_x_2027_);
v___x_2037_ = lean_array_set(v_x_2028_, v_x_2029_, v_arg_2036_);
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_sub(v_x_2029_, v___x_2038_);
v___x_2040_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_2023_, v_a_2020_, v_tacticName_2021_, v_mvarId_2022_, v_indices_2024_, v_a_2025_, v_major_2026_, v_fn_2035_, v___x_2037_, v___x_2039_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
return v___x_2040_;
}
else
{
if (lean_obj_tag(v_x_2027_) == 4)
{
lean_object* v_us_2041_; lean_object* v_recursorName_2042_; lean_object* v_univLevelPos_2043_; uint8_t v_depElim_2044_; lean_object* v_paramsPos_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___y_2049_; lean_object* v_motive_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_us_2041_ = lean_ctor_get(v_x_2027_, 1);
lean_inc(v_us_2041_);
lean_dec_ref(v_x_2027_);
v_recursorName_2042_ = lean_ctor_get(v_recursorInfo_2023_, 0);
lean_inc(v_recursorName_2042_);
v_univLevelPos_2043_ = lean_ctor_get(v_recursorInfo_2023_, 2);
lean_inc(v_univLevelPos_2043_);
v_depElim_2044_ = lean_ctor_get_uint8(v_recursorInfo_2023_, sizeof(void*)*8);
v_paramsPos_2045_ = lean_ctor_get(v_recursorInfo_2023_, 5);
lean_inc(v_paramsPos_2045_);
lean_dec_ref(v_recursorInfo_2023_);
v___x_2046_ = lean_array_mk(v_us_2041_);
v___x_2047_ = 0;
v___x_2067_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_2022_);
lean_inc(v_tacticName_2021_);
lean_inc(v_a_2020_);
v___x_2068_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_2020_, v___x_2046_, v_tacticName_2021_, v_mvarId_2022_, v___x_2067_, v_univLevelPos_2043_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v_univLevelPos_2043_);
lean_dec_ref(v___x_2046_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2115_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2068_);
v_fst_2070_ = lean_ctor_get(v_a_2069_, 0);
v_snd_2071_ = lean_ctor_get(v_a_2069_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2069_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2073_ = v_a_2069_;
v_isShared_2074_ = v_isSharedCheck_2115_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2071_);
lean_inc(v_fst_2070_);
lean_dec(v_a_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2115_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; uint8_t v___x_2095_; 
v___x_2095_ = lean_unbox(v_snd_2071_);
lean_dec(v_snd_2071_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_Level_isZero(v_a_2020_);
lean_dec(v_a_2020_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_dec(v_fst_2070_);
lean_dec(v_paramsPos_2045_);
lean_dec_ref(v_x_2028_);
lean_dec_ref(v_major_2026_);
lean_dec_ref(v_a_2025_);
v___x_2097_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2098_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2099_ = l_Lean_MessageData_ofName(v_recursorName_2042_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 7);
lean_ctor_set(v___x_2073_, 1, v___x_2099_);
lean_ctor_set(v___x_2073_, 0, v___x_2098_);
v___x_2101_ = v___x_2073_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v___x_2102_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_2021_, v_mvarId_2022_, v___x_2103_);
v___x_2105_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2097_, v___x_2104_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_del_object(v___x_2073_);
lean_dec(v_tacticName_2021_);
v___y_2076_ = v___y_2030_;
v___y_2077_ = v___y_2031_;
v___y_2078_ = v___y_2032_;
v___y_2079_ = v___y_2033_;
goto v___jp_2075_;
}
}
else
{
lean_del_object(v___x_2073_);
lean_dec(v_tacticName_2021_);
lean_dec(v_a_2020_);
v___y_2076_ = v___y_2030_;
v___y_2077_ = v___y_2031_;
v___y_2078_ = v___y_2032_;
v___y_2079_ = v___y_2033_;
goto v___jp_2075_;
}
v___jp_2075_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_array_to_list(v_fst_2070_);
v___x_2081_ = l_Lean_mkConst(v_recursorName_2042_, v___x_2080_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
v___x_2082_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_2022_, v_x_2028_, v_paramsPos_2045_, v___x_2081_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec_ref(v_x_2028_);
if (lean_obj_tag(v___x_2082_) == 0)
{
if (v_depElim_2044_ == 0)
{
lean_object* v_a_2083_; 
lean_dec_ref(v_major_2026_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2082_);
v___y_2049_ = v_a_2083_;
v_motive_2050_ = v_a_2025_;
v___y_2051_ = v___y_2076_;
v___y_2052_ = v___y_2077_;
v___y_2053_ = v___y_2078_;
v___y_2054_ = v___y_2079_;
goto v___jp_2048_;
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2085_; 
v_a_2084_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2082_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc_ref(v_major_2026_);
v___x_2085_ = lean_infer_type(v_major_2026_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = lean_unsigned_to_nat(1u);
v___x_2088_ = lean_mk_empty_array_with_capacity(v___x_2087_);
v___x_2089_ = lean_array_push(v___x_2088_, v_major_2026_);
v___x_2090_ = l_Lean_Expr_abstractM(v_a_2025_, v___x_2089_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec_ref(v___x_2089_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2093_ = 0;
v___x_2094_ = l_Lean_mkLambda(v___x_2092_, v___x_2093_, v_a_2086_, v_a_2091_);
v___y_2049_ = v_a_2084_;
v_motive_2050_ = v___x_2094_;
v___y_2051_ = v___y_2076_;
v___y_2052_ = v___y_2077_;
v___y_2053_ = v___y_2078_;
v___y_2054_ = v___y_2079_;
goto v___jp_2048_;
}
else
{
lean_dec(v_a_2086_);
lean_dec(v_a_2084_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v___x_2090_;
}
}
else
{
lean_dec(v_a_2084_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec_ref(v_major_2026_);
lean_dec_ref(v_a_2025_);
return v___x_2085_;
}
}
}
else
{
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec_ref(v_major_2026_);
lean_dec_ref(v_a_2025_);
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_paramsPos_2045_);
lean_dec(v_recursorName_2042_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v_x_2028_);
lean_dec_ref(v_major_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_mvarId_2022_);
lean_dec(v_tacticName_2021_);
lean_dec(v_a_2020_);
v_a_2116_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2068_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2068_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
v___jp_2048_:
{
uint8_t v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = 1;
v___x_2056_ = 1;
v___x_2057_ = l_Lean_Meta_mkLambdaFVars(v_indices_2024_, v_motive_2050_, v___x_2047_, v___x_2055_, v___x_2047_, v___x_2055_, v___x_2056_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2066_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = l_Lean_Expr_app___override(v___y_2049_, v_a_2058_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2062_);
v___x_2064_ = v___x_2060_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_dec_ref(v___y_2049_);
return v___x_2057_;
}
}
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref(v_x_2028_);
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_major_2026_);
lean_dec_ref(v_a_2025_);
lean_dec_ref(v_recursorInfo_2023_);
lean_dec(v_a_2020_);
v___x_2124_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2125_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_2021_, v_mvarId_2022_, v___x_2124_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2126_, lean_object* v_tacticName_2127_, lean_object* v_mvarId_2128_, lean_object* v_recursorInfo_2129_, lean_object* v_indices_2130_, lean_object* v_a_2131_, lean_object* v_major_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2126_, v_tacticName_2127_, v_mvarId_2128_, v_recursorInfo_2129_, v_indices_2130_, v_a_2131_, v_major_2132_, v_x_2133_, v_x_2134_, v_x_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v_x_2135_);
lean_dec_ref(v_indices_2130_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2142_, lean_object* v_tacticName_2143_, lean_object* v_majorFVarId_2144_, lean_object* v_recursorInfo_2145_, lean_object* v_indices_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; 
lean_inc(v_mvarId_2142_);
v___x_2152_ = l_Lean_MVarId_getType(v_mvarId_2142_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
lean_inc(v_a_2150_);
lean_inc_ref(v_a_2149_);
lean_inc(v_a_2148_);
lean_inc_ref(v_a_2147_);
lean_inc(v_a_2153_);
v___x_2154_ = l_Lean_Meta_getLevel(v_a_2153_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = l_Lean_Meta_normalizeLevel(v_a_2155_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v_major_2158_; lean_object* v___x_2159_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
lean_inc(v_majorFVarId_2144_);
v_major_2158_ = l_Lean_mkFVar(v_majorFVarId_2144_);
lean_inc_ref(v_a_2147_);
v___x_2159_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2144_, v_a_2147_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v_typeName_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
v_typeName_2161_ = lean_ctor_get(v_recursorInfo_2145_, 1);
v___x_2162_ = l_Lean_LocalDecl_type(v_a_2160_);
lean_dec(v_a_2160_);
lean_inc(v_a_2150_);
lean_inc_ref(v_a_2149_);
lean_inc(v_a_2148_);
lean_inc_ref(v_a_2147_);
lean_inc_ref(v___x_2162_);
v___x_2163_ = l_Lean_Meta_whnfUntil(v___x_2162_, v_typeName_2161_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
if (lean_obj_tag(v_a_2164_) == 1)
{
lean_object* v_val_2165_; lean_object* v_dummy_2166_; lean_object* v_nargs_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v___x_2162_);
v_val_2165_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_val_2165_);
lean_dec_ref(v_a_2164_);
v_dummy_2166_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2167_ = l_Lean_Expr_getAppNumArgs(v_val_2165_);
lean_inc(v_nargs_2167_);
v___x_2168_ = lean_mk_array(v_nargs_2167_, v_dummy_2166_);
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_sub(v_nargs_2167_, v___x_2169_);
lean_dec(v_nargs_2167_);
v___x_2171_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2157_, v_tacticName_2143_, v_mvarId_2142_, v_recursorInfo_2145_, v_indices_2146_, v_a_2153_, v_major_2158_, v_val_2165_, v___x_2168_, v___x_2170_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v___x_2170_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; 
lean_dec(v_a_2164_);
lean_dec_ref(v_major_2158_);
lean_dec(v_a_2157_);
lean_dec(v_a_2153_);
lean_dec_ref(v_recursorInfo_2145_);
v___x_2172_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2143_, v_mvarId_2142_, v___x_2162_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v___x_2172_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v___x_2162_);
lean_dec_ref(v_major_2158_);
lean_dec(v_a_2157_);
lean_dec(v_a_2153_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_recursorInfo_2145_);
lean_dec(v_tacticName_2143_);
lean_dec(v_mvarId_2142_);
v_a_2173_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2163_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2163_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_major_2158_);
lean_dec(v_a_2157_);
lean_dec(v_a_2153_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_recursorInfo_2145_);
lean_dec(v_tacticName_2143_);
lean_dec(v_mvarId_2142_);
v_a_2181_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2159_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2159_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2153_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_recursorInfo_2145_);
lean_dec(v_majorFVarId_2144_);
lean_dec(v_tacticName_2143_);
lean_dec(v_mvarId_2142_);
v_a_2189_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2156_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2156_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2153_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_recursorInfo_2145_);
lean_dec(v_majorFVarId_2144_);
lean_dec(v_tacticName_2143_);
lean_dec(v_mvarId_2142_);
v_a_2197_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2154_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2154_);
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
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_recursorInfo_2145_);
lean_dec(v_majorFVarId_2144_);
lean_dec(v_tacticName_2143_);
lean_dec(v_mvarId_2142_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2205_, lean_object* v_tacticName_2206_, lean_object* v_majorFVarId_2207_, lean_object* v_recursorInfo_2208_, lean_object* v_indices_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2205_, v_tacticName_2206_, v_majorFVarId_2207_, v_recursorInfo_2208_, v_indices_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec_ref(v_indices_2209_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2216_, lean_object* v_name_2217_, lean_object* v_msg_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2217_, v_msg_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2225_, lean_object* v_name_2226_, lean_object* v_msg_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2225_, v_name_2226_, v_msg_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2234_, v_x_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2241_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2241_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2258_, lean_object* v_x_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2258_, v_x_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2266_, lean_object* v_mvarId_2267_, lean_object* v_x_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2267_, v_x_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_mvarId_2276_, lean_object* v_x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2275_, v_mvarId_2276_, v_x_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2284_, lean_object* v_as_2285_, size_t v_sz_2286_, size_t v_i_2287_, lean_object* v_b_2288_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_usize_dec_lt(v_i_2287_, v_sz_2286_);
if (v___x_2289_ == 0)
{
return v_b_2288_;
}
else
{
lean_object* v_fst_2290_; lean_object* v_snd_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2309_; 
v_fst_2290_ = lean_ctor_get(v_b_2288_, 0);
v_snd_2291_ = lean_ctor_get(v_b_2288_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_b_2288_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2293_ = v_b_2288_;
v_isShared_2294_ = v_isSharedCheck_2309_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snd_2291_);
lean_inc(v_fst_2290_);
lean_dec(v_b_2288_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2309_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2295_ = lean_box(0);
v_a_2296_ = lean_array_uget_borrowed(v_as_2285_, v_i_2287_);
v___x_2297_ = l_Lean_Expr_fvarId_x21(v_a_2296_);
v___x_2298_ = lean_array_get_borrowed(v___x_2295_, v_fst_2284_, v_snd_2291_);
lean_inc(v___x_2298_);
v___x_2299_ = l_Lean_mkFVar(v___x_2298_);
v___x_2300_ = l_Lean_Meta_FVarSubst_insert(v_fst_2290_, v___x_2297_, v___x_2299_);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_snd_2291_, v___x_2301_);
lean_dec(v_snd_2291_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2302_);
lean_ctor_set(v___x_2293_, 0, v___x_2300_);
v___x_2304_ = v___x_2293_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
size_t v___x_2305_; size_t v___x_2306_; 
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_add(v_i_2287_, v___x_2305_);
v_i_2287_ = v___x_2306_;
v_b_2288_ = v___x_2304_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2310_, lean_object* v_as_2311_, lean_object* v_sz_2312_, lean_object* v_i_2313_, lean_object* v_b_2314_){
_start:
{
size_t v_sz_boxed_2315_; size_t v_i_boxed_2316_; lean_object* v_res_2317_; 
v_sz_boxed_2315_ = lean_unbox_usize(v_sz_2312_);
lean_dec(v_sz_2312_);
v_i_boxed_2316_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2310_, v_as_2311_, v_sz_boxed_2315_, v_i_boxed_2316_, v_b_2314_);
lean_dec_ref(v_as_2311_);
lean_dec_ref(v_fst_2310_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2318_, lean_object* v___x_2319_, lean_object* v_fst_2320_, lean_object* v_a_2321_, lean_object* v___x_2322_, lean_object* v_givenNames_2323_, lean_object* v_fst_2324_, lean_object* v___x_2325_, lean_object* v_fst_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc_ref(v_a_2321_);
lean_inc(v_snd_2318_);
v___x_2332_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2318_, v___x_2319_, v_fst_2320_, v_a_2321_, v___x_2322_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2318_, v_givenNames_2323_, v_a_2321_, v_fst_2324_, v___x_2325_, v___x_2322_, v_fst_2326_, v_a_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec_ref(v_a_2321_);
return v___x_2334_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v_fst_2326_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_a_2321_);
lean_dec(v_snd_2318_);
v_a_2335_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2332_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2332_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2343_, lean_object* v___x_2344_, lean_object* v_fst_2345_, lean_object* v_a_2346_, lean_object* v___x_2347_, lean_object* v_givenNames_2348_, lean_object* v_fst_2349_, lean_object* v___x_2350_, lean_object* v_fst_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2343_, v___x_2344_, v_fst_2345_, v_a_2346_, v___x_2347_, v_givenNames_2348_, v_fst_2349_, v___x_2350_, v_fst_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec_ref(v_fst_2349_);
lean_dec_ref(v_givenNames_2348_);
lean_dec_ref(v___x_2347_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2358_, size_t v_i_2359_, lean_object* v_bs_2360_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_usize_dec_lt(v_i_2359_, v_sz_2358_);
if (v___x_2361_ == 0)
{
return v_bs_2360_;
}
else
{
lean_object* v_v_2362_; lean_object* v___x_2363_; lean_object* v_bs_x27_2364_; lean_object* v___x_2365_; size_t v___x_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v_v_2362_ = lean_array_uget(v_bs_2360_, v_i_2359_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v_bs_x27_2364_ = lean_array_uset(v_bs_2360_, v_i_2359_, v___x_2363_);
v___x_2365_ = l_Lean_Expr_fvarId_x21(v_v_2362_);
lean_dec(v_v_2362_);
v___x_2366_ = ((size_t)1ULL);
v___x_2367_ = lean_usize_add(v_i_2359_, v___x_2366_);
v___x_2368_ = lean_array_uset(v_bs_x27_2364_, v_i_2359_, v___x_2365_);
v_i_2359_ = v___x_2367_;
v_bs_2360_ = v___x_2368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2370_, lean_object* v_i_2371_, lean_object* v_bs_2372_){
_start:
{
size_t v_sz_boxed_2373_; size_t v_i_boxed_2374_; lean_object* v_res_2375_; 
v_sz_boxed_2373_ = lean_unbox_usize(v_sz_2370_);
lean_dec(v_sz_2370_);
v_i_boxed_2374_ = lean_unbox_usize(v_i_2371_);
lean_dec(v_i_2371_);
v_res_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2373_, v_i_boxed_2374_, v_bs_2372_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2376_, lean_object* v_val_2377_, lean_object* v_mvarId_2378_, lean_object* v_as_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
if (lean_obj_tag(v_as_2379_) == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v_mvarId_2378_);
lean_dec_ref(v_val_2377_);
v___x_2385_ = lean_box(0);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
else
{
lean_object* v_head_2387_; 
v_head_2387_ = lean_ctor_get(v_as_2379_, 0);
lean_inc(v_head_2387_);
if (lean_obj_tag(v_head_2387_) == 0)
{
lean_object* v_tail_2388_; 
v_tail_2388_ = lean_ctor_get(v_as_2379_, 1);
lean_inc(v_tail_2388_);
lean_dec_ref(v_as_2379_);
v_as_2379_ = v_tail_2388_;
goto _start;
}
else
{
lean_object* v_tail_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2413_; 
v_tail_2390_ = lean_ctor_get(v_as_2379_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_as_2379_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v_as_2379_, 0);
lean_dec(v_unused_2414_);
v___x_2392_ = v_as_2379_;
v_isShared_2393_ = v_isSharedCheck_2413_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_tail_2390_);
lean_dec(v_as_2379_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2413_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_val_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2412_; 
v_val_2394_ = lean_ctor_get(v_head_2387_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_head_2387_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2396_ = v_head_2387_;
v_isShared_2397_ = v_isSharedCheck_2412_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_val_2394_);
lean_dec(v_head_2387_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2412_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = lean_array_get_size(v_majorTypeArgs_2376_);
v___x_2399_ = lean_nat_dec_le(v___x_2398_, v_val_2394_);
lean_dec(v_val_2394_);
if (v___x_2399_ == 0)
{
lean_del_object(v___x_2396_);
lean_del_object(v___x_2392_);
v_as_2379_ = v_tail_2390_;
goto _start;
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2377_);
v___x_2403_ = l_Lean_indentExpr(v_val_2377_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 7);
lean_ctor_set(v___x_2392_, 1, v___x_2403_);
lean_ctor_set(v___x_2392_, 0, v___x_2402_);
v___x_2405_ = v___x_2392_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2405_);
v___x_2407_ = v___x_2396_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; 
lean_inc(v_mvarId_2378_);
v___x_2408_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2401_, v_mvarId_2378_, v___x_2407_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_dec_ref(v___x_2408_);
v_as_2379_ = v_tail_2390_;
goto _start;
}
else
{
lean_dec(v_tail_2390_);
lean_dec(v_mvarId_2378_);
lean_dec_ref(v_val_2377_);
return v___x_2408_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2415_, lean_object* v_val_2416_, lean_object* v_mvarId_2417_, lean_object* v_as_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2415_, v_val_2416_, v_mvarId_2417_, v_as_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_majorTypeArgs_2415_);
return v_res_2424_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2427_ = l_Lean_stringToMessageData(v___x_2426_);
return v___x_2427_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2430_ = l_Lean_stringToMessageData(v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2434_, lean_object* v_val_2435_, lean_object* v_mvarId_2436_, lean_object* v_majorFVarId_2437_, lean_object* v_givenNames_2438_, lean_object* v_recursorName_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
if (lean_obj_tag(v_x_2440_) == 5)
{
lean_object* v_fn_2448_; lean_object* v_arg_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_fn_2448_ = lean_ctor_get(v_x_2440_, 0);
lean_inc_ref(v_fn_2448_);
v_arg_2449_ = lean_ctor_get(v_x_2440_, 1);
lean_inc_ref(v_arg_2449_);
lean_dec_ref(v_x_2440_);
v___x_2450_ = lean_array_set(v_x_2441_, v_x_2442_, v_arg_2449_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_sub(v_x_2442_, v___x_2451_);
lean_dec(v_x_2442_);
v_x_2440_ = v_fn_2448_;
v_x_2441_ = v___x_2450_;
v_x_2442_ = v___x_2452_;
goto _start;
}
else
{
uint8_t v_depElim_2454_; lean_object* v_paramsPos_2455_; lean_object* v___x_2456_; 
lean_dec(v_x_2442_);
lean_dec_ref(v_x_2440_);
v_depElim_2454_ = lean_ctor_get_uint8(v_a_2434_, sizeof(void*)*8);
v_paramsPos_2455_ = lean_ctor_get(v_a_2434_, 5);
lean_inc(v_paramsPos_2455_);
lean_inc(v_mvarId_2436_);
lean_inc_ref(v_val_2435_);
v___x_2456_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2441_, v_val_2435_, v_mvarId_2436_, v_paramsPos_2455_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec_ref(v_x_2441_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v___x_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; size_t v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___x_2475_; 
lean_dec_ref(v___x_2456_);
v___x_2457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v___y_2443_);
lean_inc_ref(v_a_2434_);
lean_inc(v_mvarId_2436_);
v___x_2475_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2436_, v___x_2457_, v_a_2434_, v_val_2435_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2475_);
lean_inc(v_mvarId_2436_);
v___x_2477_ = l_Lean_MVarId_getType(v_mvarId_2436_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v_cls_2479_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
v_cls_2479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2454_ == 0)
{
lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2594_; 
lean_inc(v_majorFVarId_2437_);
v___x_2571_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2478_, v_majorFVarId_2437_, v___y_2444_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2594_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2594_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
uint8_t v___x_2576_; 
v___x_2576_ = lean_unbox(v_a_2572_);
lean_dec(v_a_2572_);
if (v___x_2576_ == 0)
{
lean_del_object(v___x_2574_);
lean_dec(v_recursorName_2439_);
v___y_2481_ = v___y_2443_;
v___y_2482_ = v___y_2444_;
v___y_2483_ = v___y_2445_;
v___y_2484_ = v___y_2446_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2577_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2578_ = l_Lean_MessageData_ofName(v_recursorName_2439_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 1);
lean_ctor_set(v___x_2574_, 0, v___x_2581_);
v___x_2583_ = v___x_2574_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; 
lean_inc(v_mvarId_2436_);
v___x_2584_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2457_, v_mvarId_2436_, v___x_2583_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref(v___x_2584_);
v___y_2481_ = v___y_2443_;
v___y_2482_ = v___y_2444_;
v___y_2483_ = v___y_2445_;
v___y_2484_ = v___y_2446_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_a_2476_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec(v_mvarId_2436_);
lean_dec_ref(v_a_2434_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2478_);
lean_dec(v_recursorName_2439_);
v___y_2481_ = v___y_2443_;
v___y_2482_ = v___y_2444_;
v___y_2483_ = v___y_2445_;
v___y_2484_ = v___y_2446_;
goto v___jp_2480_;
}
v___jp_2480_:
{
size_t v_sz_2485_; size_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; 
v_sz_2485_ = lean_array_size(v_a_2476_);
v___x_2486_ = ((size_t)0ULL);
lean_inc(v_a_2476_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2485_, v___x_2486_, v_a_2476_);
lean_inc(v_majorFVarId_2437_);
v___x_2488_ = lean_array_push(v___x_2487_, v_majorFVarId_2437_);
v___x_2489_ = 1;
v___x_2490_ = 0;
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
v___x_2491_ = l_Lean_MVarId_revert(v_mvarId_2436_, v___x_2488_, v___x_2489_, v___x_2490_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v_fst_2493_; lean_object* v_snd_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref(v___x_2491_);
v_fst_2493_ = lean_ctor_get(v_a_2492_, 0);
lean_inc(v_fst_2493_);
v_snd_2494_ = lean_ctor_get(v_a_2492_, 1);
lean_inc(v_snd_2494_);
lean_dec(v_a_2492_);
v___x_2495_ = lean_array_get_size(v_a_2476_);
v___x_2496_ = lean_box(0);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
v___x_2497_ = l_Lean_Meta_introNCore(v_snd_2494_, v___x_2495_, v___x_2496_, v___x_2490_, v___x_2489_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v_fst_2499_; lean_object* v_snd_2500_; lean_object* v___x_2501_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
v_fst_2499_ = lean_ctor_get(v_a_2498_, 0);
lean_inc(v_fst_2499_);
v_snd_2500_ = lean_ctor_get(v_a_2498_, 1);
lean_inc(v_snd_2500_);
lean_dec(v_a_2498_);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
v___x_2501_ = l_Lean_Meta_intro1Core(v_snd_2500_, v___x_2489_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2546_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref(v___x_2501_);
v_fst_2503_ = lean_ctor_get(v_a_2502_, 0);
v_snd_2504_ = lean_ctor_get(v_a_2502_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_a_2502_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2506_ = v_a_2502_;
v_isShared_2507_ = v_isSharedCheck_2546_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_snd_2504_);
lean_inc(v_fst_2503_);
lean_dec(v_a_2502_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2546_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2545_; 
v___x_2508_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v_cls_2479_, v___y_2483_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2545_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2545_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2513_ = lean_box(0);
lean_inc(v_fst_2503_);
v___x_2514_ = l_Lean_mkFVar(v_fst_2503_);
lean_inc_ref(v___x_2514_);
v___x_2515_ = l_Lean_Meta_FVarSubst_insert(v___x_2513_, v_majorFVarId_2437_, v___x_2514_);
v___x_2516_ = lean_unsigned_to_nat(0u);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2516_);
lean_ctor_set(v___x_2506_, 0, v___x_2515_);
v___x_2518_ = v___x_2506_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2499_, v_a_2476_, v_sz_2485_, v___x_2486_, v___x_2518_);
lean_dec(v_a_2476_);
v___x_2520_ = lean_unbox(v_a_2509_);
lean_dec(v_a_2509_);
if (v___x_2520_ == 0)
{
lean_object* v_fst_2521_; 
lean_del_object(v___x_2511_);
v_fst_2521_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_fst_2521_);
lean_dec_ref(v___x_2519_);
lean_inc(v_snd_2504_);
v___y_2459_ = v___x_2514_;
v___y_2460_ = v_fst_2521_;
v___y_2461_ = v_fst_2503_;
v___y_2462_ = v_snd_2504_;
v___y_2463_ = v_fst_2493_;
v___y_2464_ = v___x_2486_;
v___y_2465_ = v_snd_2504_;
v___y_2466_ = v_fst_2499_;
v___y_2467_ = v___y_2481_;
v___y_2468_ = v___y_2482_;
v___y_2469_ = v___y_2483_;
v___y_2470_ = v___y_2484_;
goto v___jp_2458_;
}
else
{
lean_object* v_fst_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2542_; 
v_fst_2522_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2519_, 1);
lean_dec(v_unused_2543_);
v___x_2524_ = v___x_2519_;
v_isShared_2525_ = v_isSharedCheck_2542_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_fst_2522_);
lean_dec(v___x_2519_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2542_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2504_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
lean_ctor_set(v___x_2511_, 0, v_snd_2504_);
v___x_2528_ = v___x_2511_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_snd_2504_);
v___x_2528_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 7);
lean_ctor_set(v___x_2524_, 1, v___x_2528_);
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v_cls_2479_, v___x_2530_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref(v___x_2531_);
lean_inc(v_snd_2504_);
v___y_2459_ = v___x_2514_;
v___y_2460_ = v_fst_2522_;
v___y_2461_ = v_fst_2503_;
v___y_2462_ = v_snd_2504_;
v___y_2463_ = v_fst_2493_;
v___y_2464_ = v___x_2486_;
v___y_2465_ = v_snd_2504_;
v___y_2466_ = v_fst_2499_;
v___y_2467_ = v___y_2481_;
v___y_2468_ = v___y_2482_;
v___y_2469_ = v___y_2483_;
v___y_2470_ = v___y_2484_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_fst_2522_);
lean_dec_ref(v___x_2514_);
lean_dec(v_snd_2504_);
lean_dec(v_fst_2503_);
lean_dec(v_fst_2499_);
lean_dec(v_fst_2493_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v_givenNames_2438_);
lean_dec_ref(v_a_2434_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
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
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_fst_2499_);
lean_dec(v_fst_2493_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec_ref(v_a_2434_);
v_a_2547_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2501_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2501_);
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
lean_dec(v_fst_2493_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec_ref(v_a_2434_);
v_a_2555_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2497_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2497_);
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
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec_ref(v_a_2434_);
v_a_2563_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2491_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2491_);
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
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_a_2476_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_recursorName_2439_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec(v_mvarId_2436_);
lean_dec_ref(v_a_2434_);
v_a_2595_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2477_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2477_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_recursorName_2439_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec(v_mvarId_2436_);
lean_dec_ref(v_a_2434_);
v_a_2603_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2475_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2475_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
v___jp_2458_:
{
size_t v_sz_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; 
v_sz_2471_ = lean_array_size(v___y_2466_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_sz_2471_, v___y_2464_, v___y_2466_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2473_, 0, v___y_2462_);
lean_closure_set(v___f_2473_, 1, v___x_2457_);
lean_closure_set(v___f_2473_, 2, v___y_2461_);
lean_closure_set(v___f_2473_, 3, v_a_2434_);
lean_closure_set(v___f_2473_, 4, v___x_2472_);
lean_closure_set(v___f_2473_, 5, v_givenNames_2438_);
lean_closure_set(v___f_2473_, 6, v___y_2463_);
lean_closure_set(v___f_2473_, 7, v___y_2459_);
lean_closure_set(v___f_2473_, 8, v___y_2460_);
v___x_2474_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2465_, v___f_2473_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2474_;
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_recursorName_2439_);
lean_dec_ref(v_givenNames_2438_);
lean_dec(v_majorFVarId_2437_);
lean_dec(v_mvarId_2436_);
lean_dec_ref(v_val_2435_);
lean_dec_ref(v_a_2434_);
v_a_2611_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2456_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2456_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2619_, lean_object* v_val_2620_, lean_object* v_mvarId_2621_, lean_object* v_majorFVarId_2622_, lean_object* v_givenNames_2623_, lean_object* v_recursorName_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2619_, v_val_2620_, v_mvarId_2621_, v_majorFVarId_2622_, v_givenNames_2623_, v_recursorName_2624_, v_x_2625_, v_x_2626_, v_x_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2634_, lean_object* v_mvarId_2635_, lean_object* v_a_2636_, lean_object* v_majorFVarId_2637_, lean_object* v_givenNames_2638_, lean_object* v_recursorName_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
if (lean_obj_tag(v_x_2640_) == 5)
{
lean_object* v_fn_2648_; lean_object* v_arg_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_fn_2648_ = lean_ctor_get(v_x_2640_, 0);
lean_inc_ref(v_fn_2648_);
v_arg_2649_ = lean_ctor_get(v_x_2640_, 1);
lean_inc_ref(v_arg_2649_);
lean_dec_ref(v_x_2640_);
v___x_2650_ = lean_array_set(v_x_2641_, v_x_2642_, v_arg_2649_);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = lean_nat_sub(v_x_2642_, v___x_2651_);
v___x_2653_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2636_, v_val_2634_, v_mvarId_2635_, v_majorFVarId_2637_, v_givenNames_2638_, v_recursorName_2639_, v_fn_2648_, v___x_2650_, v___x_2652_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2653_;
}
else
{
uint8_t v_depElim_2654_; lean_object* v_paramsPos_2655_; lean_object* v___x_2656_; 
lean_dec_ref(v_x_2640_);
v_depElim_2654_ = lean_ctor_get_uint8(v_a_2636_, sizeof(void*)*8);
v_paramsPos_2655_ = lean_ctor_get(v_a_2636_, 5);
lean_inc(v_paramsPos_2655_);
lean_inc(v_mvarId_2635_);
lean_inc_ref(v_val_2634_);
v___x_2656_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2641_, v_val_2634_, v_mvarId_2635_, v_paramsPos_2655_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec_ref(v_x_2641_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; size_t v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___x_2675_; 
lean_dec_ref(v___x_2656_);
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v___y_2643_);
lean_inc_ref(v_a_2636_);
lean_inc(v_mvarId_2635_);
v___x_2675_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2635_, v___x_2657_, v_a_2636_, v_val_2634_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
lean_inc(v_mvarId_2635_);
v___x_2677_ = l_Lean_MVarId_getType(v_mvarId_2635_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v_cls_2679_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2677_);
v_cls_2679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2654_ == 0)
{
lean_object* v___x_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2794_; 
lean_inc(v_majorFVarId_2637_);
v___x_2771_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2678_, v_majorFVarId_2637_, v___y_2644_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2794_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2794_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_unbox(v_a_2772_);
lean_dec(v_a_2772_);
if (v___x_2776_ == 0)
{
lean_del_object(v___x_2774_);
lean_dec(v_recursorName_2639_);
v___y_2681_ = v___y_2643_;
v___y_2682_ = v___y_2644_;
v___y_2683_ = v___y_2645_;
v___y_2684_ = v___y_2646_;
goto v___jp_2680_;
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2777_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2778_ = l_Lean_MessageData_ofName(v_recursorName_2639_);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2781_);
v___x_2783_ = v___x_2774_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; 
lean_inc(v_mvarId_2635_);
v___x_2784_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2657_, v_mvarId_2635_, v___x_2783_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref(v___x_2784_);
v___y_2681_ = v___y_2643_;
v___y_2682_ = v___y_2644_;
v___y_2683_ = v___y_2645_;
v___y_2684_ = v___y_2646_;
goto v___jp_2680_;
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_a_2676_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_mvarId_2635_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2678_);
lean_dec(v_recursorName_2639_);
v___y_2681_ = v___y_2643_;
v___y_2682_ = v___y_2644_;
v___y_2683_ = v___y_2645_;
v___y_2684_ = v___y_2646_;
goto v___jp_2680_;
}
v___jp_2680_:
{
size_t v_sz_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; 
v_sz_2685_ = lean_array_size(v_a_2676_);
v___x_2686_ = ((size_t)0ULL);
lean_inc(v_a_2676_);
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2685_, v___x_2686_, v_a_2676_);
lean_inc(v_majorFVarId_2637_);
v___x_2688_ = lean_array_push(v___x_2687_, v_majorFVarId_2637_);
v___x_2689_ = 1;
v___x_2690_ = 0;
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
v___x_2691_ = l_Lean_MVarId_revert(v_mvarId_2635_, v___x_2688_, v___x_2689_, v___x_2690_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v_fst_2693_; lean_object* v_snd_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v_fst_2693_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_fst_2693_);
v_snd_2694_ = lean_ctor_get(v_a_2692_, 1);
lean_inc(v_snd_2694_);
lean_dec(v_a_2692_);
v___x_2695_ = lean_array_get_size(v_a_2676_);
v___x_2696_ = lean_box(0);
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
v___x_2697_ = l_Lean_Meta_introNCore(v_snd_2694_, v___x_2695_, v___x_2696_, v___x_2690_, v___x_2689_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v_fst_2699_; lean_object* v_snd_2700_; lean_object* v___x_2701_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2697_);
v_fst_2699_ = lean_ctor_get(v_a_2698_, 0);
lean_inc(v_fst_2699_);
v_snd_2700_ = lean_ctor_get(v_a_2698_, 1);
lean_inc(v_snd_2700_);
lean_dec(v_a_2698_);
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
v___x_2701_ = l_Lean_Meta_intro1Core(v_snd_2700_, v___x_2689_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v_fst_2703_; lean_object* v_snd_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2746_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v_fst_2703_ = lean_ctor_get(v_a_2702_, 0);
v_snd_2704_ = lean_ctor_get(v_a_2702_, 1);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_a_2702_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2706_ = v_a_2702_;
v_isShared_2707_ = v_isSharedCheck_2746_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_snd_2704_);
lean_inc(v_fst_2703_);
lean_dec(v_a_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2746_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2745_; 
v___x_2708_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v_cls_2679_, v___y_2683_);
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2745_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2745_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2713_ = lean_box(0);
lean_inc(v_fst_2703_);
v___x_2714_ = l_Lean_mkFVar(v_fst_2703_);
lean_inc_ref(v___x_2714_);
v___x_2715_ = l_Lean_Meta_FVarSubst_insert(v___x_2713_, v_majorFVarId_2637_, v___x_2714_);
v___x_2716_ = lean_unsigned_to_nat(0u);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v___x_2716_);
lean_ctor_set(v___x_2706_, 0, v___x_2715_);
v___x_2718_ = v___x_2706_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2699_, v_a_2676_, v_sz_2685_, v___x_2686_, v___x_2718_);
lean_dec(v_a_2676_);
v___x_2720_ = lean_unbox(v_a_2709_);
lean_dec(v_a_2709_);
if (v___x_2720_ == 0)
{
lean_object* v_fst_2721_; 
lean_del_object(v___x_2711_);
v_fst_2721_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_fst_2721_);
lean_dec_ref(v___x_2719_);
lean_inc(v_snd_2704_);
v___y_2659_ = v_fst_2703_;
v___y_2660_ = v___x_2714_;
v___y_2661_ = v_fst_2693_;
v___y_2662_ = v_snd_2704_;
v___y_2663_ = v_fst_2721_;
v___y_2664_ = v___x_2686_;
v___y_2665_ = v_fst_2699_;
v___y_2666_ = v_snd_2704_;
v___y_2667_ = v___y_2681_;
v___y_2668_ = v___y_2682_;
v___y_2669_ = v___y_2683_;
v___y_2670_ = v___y_2684_;
goto v___jp_2658_;
}
else
{
lean_object* v_fst_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2742_; 
v_fst_2722_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v___x_2719_, 1);
lean_dec(v_unused_2743_);
v___x_2724_ = v___x_2719_;
v_isShared_2725_ = v_isSharedCheck_2742_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_fst_2722_);
lean_dec(v___x_2719_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2742_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2704_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 1);
lean_ctor_set(v___x_2711_, 0, v_snd_2704_);
v___x_2728_ = v___x_2711_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_snd_2704_);
v___x_2728_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 7);
lean_ctor_set(v___x_2724_, 1, v___x_2728_);
lean_ctor_set(v___x_2724_, 0, v___x_2726_);
v___x_2730_ = v___x_2724_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v_cls_2679_, v___x_2730_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_dec_ref(v___x_2731_);
lean_inc(v_snd_2704_);
v___y_2659_ = v_fst_2703_;
v___y_2660_ = v___x_2714_;
v___y_2661_ = v_fst_2693_;
v___y_2662_ = v_snd_2704_;
v___y_2663_ = v_fst_2722_;
v___y_2664_ = v___x_2686_;
v___y_2665_ = v_fst_2699_;
v___y_2666_ = v_snd_2704_;
v___y_2667_ = v___y_2681_;
v___y_2668_ = v___y_2682_;
v___y_2669_ = v___y_2683_;
v___y_2670_ = v___y_2684_;
goto v___jp_2658_;
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_fst_2722_);
lean_dec_ref(v___x_2714_);
lean_dec(v_snd_2704_);
lean_dec(v_fst_2703_);
lean_dec(v_fst_2699_);
lean_dec(v_fst_2693_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec_ref(v_givenNames_2638_);
lean_dec_ref(v_a_2636_);
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
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
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_fst_2699_);
lean_dec(v_fst_2693_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v_a_2676_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
v_a_2747_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2701_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2701_);
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
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_fst_2693_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v_a_2676_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
v_a_2755_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2697_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2697_);
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
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v_a_2676_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
v_a_2763_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2691_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2691_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2676_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v_recursorName_2639_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_mvarId_2635_);
v_a_2795_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2677_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2677_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v_recursorName_2639_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_mvarId_2635_);
v_a_2803_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2675_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2675_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
v___jp_2658_:
{
size_t v_sz_2671_; lean_object* v___x_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; 
v_sz_2671_ = lean_array_size(v___y_2665_);
v___x_2672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_sz_2671_, v___y_2664_, v___y_2665_);
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2673_, 0, v___y_2662_);
lean_closure_set(v___f_2673_, 1, v___x_2657_);
lean_closure_set(v___f_2673_, 2, v___y_2659_);
lean_closure_set(v___f_2673_, 3, v_a_2636_);
lean_closure_set(v___f_2673_, 4, v___x_2672_);
lean_closure_set(v___f_2673_, 5, v_givenNames_2638_);
lean_closure_set(v___f_2673_, 6, v___y_2661_);
lean_closure_set(v___f_2673_, 7, v___y_2660_);
lean_closure_set(v___f_2673_, 8, v___y_2663_);
v___x_2674_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2666_, v___f_2673_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v___x_2674_;
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v_recursorName_2639_);
lean_dec_ref(v_givenNames_2638_);
lean_dec(v_majorFVarId_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_mvarId_2635_);
lean_dec_ref(v_val_2634_);
v_a_2811_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2656_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2656_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2819_, lean_object* v_mvarId_2820_, lean_object* v_a_2821_, lean_object* v_majorFVarId_2822_, lean_object* v_givenNames_2823_, lean_object* v_recursorName_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2819_, v_mvarId_2820_, v_a_2821_, v_majorFVarId_2822_, v_givenNames_2823_, v_recursorName_2824_, v_x_2825_, v_x_2826_, v_x_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v_x_2827_);
return v_res_2833_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v_cls_2837_, lean_object* v___x_2838_, lean_object* v_mvarId_2839_, lean_object* v_majorFVarId_2840_, lean_object* v_recursorName_2841_, lean_object* v_givenNames_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___x_2904_; lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2924_; 
lean_inc(v_cls_2837_);
v___x_2904_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___redArg(v_cls_2837_, v___y_2845_);
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2924_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2924_;
goto v_resetjp_2906_;
}
v___jp_2848_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = l_Lean_Name_mkStr1(v___x_2838_);
lean_inc(v___x_2853_);
lean_inc(v_mvarId_2839_);
v___x_2854_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2839_, v___x_2853_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v___x_2854_);
lean_inc_ref(v___y_2849_);
lean_inc(v_majorFVarId_2840_);
v___x_2855_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2840_, v___y_2849_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = lean_box(0);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v_recursorName_2841_);
v___x_2858_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2841_, v___x_2857_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v_typeName_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2858_);
v_typeName_2860_ = lean_ctor_get(v_a_2859_, 1);
v___x_2861_ = l_Lean_LocalDecl_type(v_a_2856_);
lean_dec(v_a_2856_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc_ref(v___x_2861_);
v___x_2862_ = l_Lean_Meta_whnfUntil(v___x_2861_, v_typeName_2860_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
if (lean_obj_tag(v_a_2863_) == 1)
{
lean_object* v_val_2864_; lean_object* v_dummy_2865_; lean_object* v_nargs_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec_ref(v___x_2861_);
lean_dec(v___x_2853_);
v_val_2864_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_val_2864_);
lean_dec_ref(v_a_2863_);
v_dummy_2865_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2866_ = l_Lean_Expr_getAppNumArgs(v_val_2864_);
lean_inc(v_nargs_2866_);
v___x_2867_ = lean_mk_array(v_nargs_2866_, v_dummy_2865_);
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_sub(v_nargs_2866_, v___x_2868_);
lean_dec(v_nargs_2866_);
lean_inc(v_val_2864_);
v___x_2870_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2864_, v_mvarId_2839_, v_a_2859_, v_majorFVarId_2840_, v_givenNames_2842_, v_recursorName_2841_, v_val_2864_, v___x_2867_, v___x_2869_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___x_2869_);
return v___x_2870_;
}
else
{
lean_object* v___x_2871_; 
lean_dec(v_a_2863_);
lean_dec(v_a_2859_);
lean_dec_ref(v_givenNames_2842_);
lean_dec(v_recursorName_2841_);
lean_dec(v_majorFVarId_2840_);
v___x_2871_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2853_, v_mvarId_2839_, v___x_2861_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
return v___x_2871_;
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec_ref(v___x_2861_);
lean_dec(v_a_2859_);
lean_dec(v___x_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_givenNames_2842_);
lean_dec(v_recursorName_2841_);
lean_dec(v_majorFVarId_2840_);
lean_dec(v_mvarId_2839_);
v_a_2872_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2862_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2862_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2856_);
lean_dec(v___x_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_givenNames_2842_);
lean_dec(v_recursorName_2841_);
lean_dec(v_majorFVarId_2840_);
lean_dec(v_mvarId_2839_);
v_a_2880_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2858_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2858_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v___x_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_givenNames_2842_);
lean_dec(v_recursorName_2841_);
lean_dec(v_majorFVarId_2840_);
lean_dec(v_mvarId_2839_);
v_a_2888_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2855_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2855_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___x_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_givenNames_2842_);
lean_dec(v_recursorName_2841_);
lean_dec(v_majorFVarId_2840_);
lean_dec(v_mvarId_2839_);
v_a_2896_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2854_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2854_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
v_resetjp_2906_:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_unbox(v_a_2905_);
lean_dec(v_a_2905_);
if (v___x_2909_ == 0)
{
lean_del_object(v___x_2907_);
lean_dec(v_cls_2837_);
v___y_2849_ = v___y_2843_;
v___y_2850_ = v___y_2844_;
v___y_2851_ = v___y_2845_;
v___y_2852_ = v___y_2846_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2839_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set_tag(v___x_2907_, 1);
lean_ctor_set(v___x_2907_, 0, v_mvarId_2839_);
v___x_2912_ = v___x_2907_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_mvarId_2839_);
v___x_2912_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2910_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v_cls_2837_, v___x_2913_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_dec_ref(v___x_2914_);
v___y_2849_ = v___y_2843_;
v___y_2850_ = v___y_2844_;
v___y_2851_ = v___y_2845_;
v___y_2852_ = v___y_2846_;
goto v___jp_2848_;
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v_givenNames_2842_);
lean_dec(v_recursorName_2841_);
lean_dec(v_majorFVarId_2840_);
lean_dec(v_mvarId_2839_);
lean_dec_ref(v___x_2838_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v_cls_2925_, lean_object* v___x_2926_, lean_object* v_mvarId_2927_, lean_object* v_majorFVarId_2928_, lean_object* v_recursorName_2929_, lean_object* v_givenNames_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_MVarId_induction___lam__0(v_cls_2925_, v___x_2926_, v_mvarId_2927_, v_majorFVarId_2928_, v_recursorName_2929_, v_givenNames_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2937_, lean_object* v_majorFVarId_2938_, lean_object* v_recursorName_2939_, lean_object* v_givenNames_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v___x_2946_; lean_object* v_cls_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2937_);
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2948_, 0, v_cls_2947_);
lean_closure_set(v___f_2948_, 1, v___x_2946_);
lean_closure_set(v___f_2948_, 2, v_mvarId_2937_);
lean_closure_set(v___f_2948_, 3, v_majorFVarId_2938_);
lean_closure_set(v___f_2948_, 4, v_recursorName_2939_);
lean_closure_set(v___f_2948_, 5, v_givenNames_2940_);
v___x_2949_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2937_, v___f_2948_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2950_, lean_object* v_majorFVarId_2951_, lean_object* v_recursorName_2952_, lean_object* v_givenNames_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_MVarId_induction(v_mvarId_2950_, v_majorFVarId_2951_, v_recursorName_2952_, v_givenNames_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
return v_res_2959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3007_ = lean_unsigned_to_nat(2221195325u);
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_3009_ = l_Lean_Name_num___override(v___x_3008_, v___x_3007_);
return v___x_3009_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_3012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3013_ = l_Lean_Name_str___override(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_3016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3017_ = l_Lean_Name_str___override(v___x_3016_, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = lean_unsigned_to_nat(2u);
v___x_3019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3020_ = l_Lean_Name_num___override(v___x_3019_, v___x_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_3023_ = 0;
v___x_3024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3025_ = l_Lean_registerTraceClass(v___x_3022_, v___x_3023_, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_3027_;
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
