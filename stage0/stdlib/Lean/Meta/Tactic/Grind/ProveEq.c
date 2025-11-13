// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProveEq
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Simp
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_proveEq_x3f___closed__1;
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_Context_ctorIdx(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_State_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_State_ctorIdx(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_Context_ctorIdx___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_proveEq_x3f___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1;
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_withoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_11);
x_15 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(x_1, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Meta_Grind_preprocessLight(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
lean_inc(x_18);
x_21 = lean_grind_internalize(x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(x_1, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_Lean_Meta_Grind_preprocessLight(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_box(0);
lean_inc(x_33);
x_36 = lean_grind_internalize(x_33, x_34, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_37 = x_36;
} else {
 lean_dec_ref(x_36);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_33);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
else
{
lean_object* x_42; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_1);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_11, 0);
lean_inc(x_44);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_Context_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_Context_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_Context_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_AbstractM_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(x_1, x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = lean_apply_11(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
x_16 = lean_apply_11(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1;
lean_inc(x_1);
x_9 = lean_name_append_index_after(x_8, x_1);
x_10 = 0;
x_11 = l_Lean_mkLambda(x_9, x_10, x_7, x_5);
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(x_3, x_1, x_4, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(x_3, x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_306; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_306 = lean_unbox(x_68);
lean_dec(x_68);
if (x_306 == 0)
{
lean_free_object(x_66);
lean_free_object(x_63);
x_70 = x_3;
x_71 = x_5;
x_72 = x_6;
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
x_79 = lean_box(0);
goto block_305;
}
else
{
uint8_t x_307; 
x_307 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_307 == 0)
{
uint8_t x_308; 
x_308 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_308 == 0)
{
lean_object* x_309; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_1);
x_309 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec_ref(x_309);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_311 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_313 = lean_grind_process_new_facts(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
lean_dec_ref(x_313);
x_314 = l_Lean_Meta_Grind_isEqv___redArg(x_310, x_312, x_5);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec_ref(x_314);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_66);
lean_free_object(x_63);
x_70 = x_3;
x_71 = x_5;
x_72 = x_6;
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
x_79 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_317; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_312);
lean_inc(x_310);
x_317 = l_Lean_Meta_Grind_hasSameType(x_310, x_312, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
lean_dec_ref(x_317);
x_319 = lean_unbox(x_318);
lean_dec(x_318);
if (x_319 == 0)
{
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_66);
lean_free_object(x_63);
x_70 = x_3;
x_71 = x_5;
x_72 = x_6;
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
x_79 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_320; 
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc(x_310);
x_320 = lean_infer_type(x_310, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
uint8_t x_322; 
x_322 = !lean_is_exclusive(x_69);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_320, 0);
x_324 = lean_ctor_get(x_69, 1);
x_325 = lean_ctor_get(x_69, 2);
x_326 = lean_ctor_get(x_69, 3);
x_327 = lean_array_get_size(x_324);
x_328 = lean_nat_add(x_327, x_3);
lean_dec(x_327);
x_329 = lean_array_push(x_324, x_323);
x_330 = lean_array_push(x_325, x_310);
x_331 = lean_array_push(x_326, x_312);
lean_ctor_set(x_69, 3, x_331);
lean_ctor_set(x_69, 2, x_330);
lean_ctor_set(x_69, 1, x_329);
x_332 = l_Lean_mkBVar(x_328);
lean_ctor_set(x_66, 0, x_332);
lean_ctor_set(x_320, 0, x_63);
return x_320;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_333 = lean_ctor_get(x_320, 0);
x_334 = lean_ctor_get(x_69, 0);
x_335 = lean_ctor_get(x_69, 1);
x_336 = lean_ctor_get(x_69, 2);
x_337 = lean_ctor_get(x_69, 3);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_69);
x_338 = lean_array_get_size(x_335);
x_339 = lean_nat_add(x_338, x_3);
lean_dec(x_338);
x_340 = lean_array_push(x_335, x_333);
x_341 = lean_array_push(x_336, x_310);
x_342 = lean_array_push(x_337, x_312);
x_343 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_343, 0, x_334);
lean_ctor_set(x_343, 1, x_340);
lean_ctor_set(x_343, 2, x_341);
lean_ctor_set(x_343, 3, x_342);
x_344 = l_Lean_mkBVar(x_339);
lean_ctor_set(x_66, 1, x_343);
lean_ctor_set(x_66, 0, x_344);
lean_ctor_set(x_320, 0, x_63);
return x_320;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_345 = lean_ctor_get(x_320, 0);
lean_inc(x_345);
lean_dec(x_320);
x_346 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_346);
x_347 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_347);
x_348 = lean_ctor_get(x_69, 2);
lean_inc_ref(x_348);
x_349 = lean_ctor_get(x_69, 3);
lean_inc_ref(x_349);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 x_350 = x_69;
} else {
 lean_dec_ref(x_69);
 x_350 = lean_box(0);
}
x_351 = lean_array_get_size(x_347);
x_352 = lean_nat_add(x_351, x_3);
lean_dec(x_351);
x_353 = lean_array_push(x_347, x_345);
x_354 = lean_array_push(x_348, x_310);
x_355 = lean_array_push(x_349, x_312);
if (lean_is_scalar(x_350)) {
 x_356 = lean_alloc_ctor(0, 4, 0);
} else {
 x_356 = x_350;
}
lean_ctor_set(x_356, 0, x_346);
lean_ctor_set(x_356, 1, x_353);
lean_ctor_set(x_356, 2, x_354);
lean_ctor_set(x_356, 3, x_355);
x_357 = l_Lean_mkBVar(x_352);
lean_ctor_set(x_66, 1, x_356);
lean_ctor_set(x_66, 0, x_357);
x_358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_358, 0, x_63);
return x_358;
}
}
else
{
uint8_t x_359; 
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_66);
lean_dec(x_69);
lean_free_object(x_63);
x_359 = !lean_is_exclusive(x_320);
if (x_359 == 0)
{
return x_320;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_320, 0);
lean_inc(x_360);
lean_dec(x_320);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
return x_361;
}
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_66);
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_362 = !lean_is_exclusive(x_317);
if (x_362 == 0)
{
return x_317;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_317, 0);
lean_inc(x_363);
lean_dec(x_317);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_66);
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_365 = !lean_is_exclusive(x_314);
if (x_365 == 0)
{
return x_314;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_314, 0);
lean_inc(x_366);
lean_dec(x_314);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
return x_367;
}
}
}
else
{
uint8_t x_368; 
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_66);
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_368 = !lean_is_exclusive(x_313);
if (x_368 == 0)
{
return x_313;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_313, 0);
lean_inc(x_369);
lean_dec(x_313);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_310);
lean_free_object(x_66);
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_371 = !lean_is_exclusive(x_311);
if (x_371 == 0)
{
return x_311;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_311, 0);
lean_inc(x_372);
lean_dec(x_311);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_free_object(x_66);
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_374 = !lean_is_exclusive(x_309);
if (x_374 == 0)
{
return x_309;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_309, 0);
lean_inc(x_375);
lean_dec(x_309);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
}
}
else
{
lean_free_object(x_66);
lean_free_object(x_63);
x_70 = x_3;
x_71 = x_5;
x_72 = x_6;
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
x_79 = lean_box(0);
goto block_305;
}
}
else
{
lean_free_object(x_66);
lean_free_object(x_63);
x_70 = x_3;
x_71 = x_5;
x_72 = x_6;
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
x_79 = lean_box(0);
goto block_305;
}
}
block_305:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
x_80 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_81);
lean_dec_ref(x_1);
x_82 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_2);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_84 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_80, x_82, x_70, x_69, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_83);
lean_dec_ref(x_81);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_81, x_83, x_70, x_88, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_dec(x_87);
return x_89;
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = l_Lean_Expr_app___override(x_87, x_96);
lean_ctor_set(x_94, 0, x_97);
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = l_Lean_Expr_app___override(x_87, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_90, 0, x_101);
return x_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Expr_app___override(x_87, x_103);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_89, 0, x_108);
return x_89;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_89);
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_110 = x_90;
} else {
 lean_dec_ref(x_90);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_113 = x_109;
} else {
 lean_dec_ref(x_109);
 x_113 = lean_box(0);
}
x_114 = l_Lean_Expr_app___override(x_87, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_110;
}
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
else
{
lean_dec(x_87);
return x_89;
}
}
}
else
{
lean_dec_ref(x_83);
lean_dec_ref(x_81);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_84;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_118 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_64;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_64);
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_122);
x_123 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_125);
lean_dec_ref(x_2);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_126 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_121, x_124, x_70, x_69, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_dec_ref(x_125);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_70, x_131);
x_133 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_122, x_125, x_132, x_130, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_dec(x_129);
lean_dec(x_120);
return x_133;
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_133, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_134);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_134, 0);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = l_Lean_mkLambda(x_120, x_123, x_129, x_140);
lean_ctor_set(x_138, 0, x_141);
return x_133;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = l_Lean_mkLambda(x_120, x_123, x_129, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_134, 0, x_145);
return x_133;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_134, 0);
lean_inc(x_146);
lean_dec(x_134);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = l_Lean_mkLambda(x_120, x_123, x_129, x_147);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_133, 0, x_152);
return x_133;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_133);
x_153 = lean_ctor_get(x_134, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_154 = x_134;
} else {
 lean_dec_ref(x_134);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_157 = x_153;
} else {
 lean_dec_ref(x_153);
 x_157 = lean_box(0);
}
x_158 = l_Lean_mkLambda(x_120, x_123, x_129, x_155);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
else
{
lean_dec(x_129);
lean_dec(x_120);
return x_133;
}
}
}
else
{
lean_dec_ref(x_125);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_126;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_162 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_163 = lean_alloc_ctor(0, 1, 0);
} else {
 x_163 = x_64;
}
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_64);
x_164 = lean_ctor_get(x_1, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_166);
x_167 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_168 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_169);
lean_dec_ref(x_2);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_170 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_165, x_168, x_70, x_69, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_dec_ref(x_169);
lean_dec_ref(x_166);
lean_dec(x_164);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_170;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_70, x_175);
x_177 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_166, x_169, x_176, x_174, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_dec(x_173);
lean_dec(x_164);
return x_177;
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_177, 0);
lean_dec(x_180);
x_181 = !lean_is_exclusive(x_178);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_178, 0);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = l_Lean_mkForall(x_164, x_167, x_173, x_184);
lean_ctor_set(x_182, 0, x_185);
return x_177;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_182, 0);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_182);
x_188 = l_Lean_mkForall(x_164, x_167, x_173, x_186);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_178, 0, x_189);
return x_177;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_178, 0);
lean_inc(x_190);
lean_dec(x_178);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_194 = l_Lean_mkForall(x_164, x_167, x_173, x_191);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_177, 0, x_196);
return x_177;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_177);
x_197 = lean_ctor_get(x_178, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_198 = x_178;
} else {
 lean_dec_ref(x_178);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_201 = x_197;
} else {
 lean_dec_ref(x_197);
 x_201 = lean_box(0);
}
x_202 = l_Lean_mkForall(x_164, x_167, x_173, x_199);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
if (lean_is_scalar(x_198)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_198;
}
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
else
{
lean_dec(x_173);
lean_dec(x_164);
return x_177;
}
}
}
else
{
lean_dec_ref(x_169);
lean_dec_ref(x_166);
lean_dec(x_164);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_170;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_206 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_207 = lean_alloc_ctor(0, 1, 0);
} else {
 x_207 = x_64;
}
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_64);
x_208 = lean_ctor_get(x_1, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_211);
x_212 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec_ref(x_1);
x_213 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_215);
lean_dec_ref(x_2);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_216 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_209, x_213, x_70, x_69, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec(x_208);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_216;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_221 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_210, x_214, x_70, x_220, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_dec(x_219);
lean_dec_ref(x_215);
lean_dec_ref(x_211);
lean_dec(x_208);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_221;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_nat_add(x_70, x_226);
x_228 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_211, x_215, x_227, x_225, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
lean_dec(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_dec(x_224);
lean_dec(x_219);
lean_dec(x_208);
return x_228;
}
else
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_228);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_228, 0);
lean_dec(x_231);
x_232 = !lean_is_exclusive(x_229);
if (x_232 == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_229, 0);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = l_Lean_Expr_letE___override(x_208, x_219, x_224, x_235, x_212);
lean_ctor_set(x_233, 0, x_236);
return x_228;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_233, 0);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_233);
x_239 = l_Lean_Expr_letE___override(x_208, x_219, x_224, x_237, x_212);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_229, 0, x_240);
return x_228;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_241 = lean_ctor_get(x_229, 0);
lean_inc(x_241);
lean_dec(x_229);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
x_245 = l_Lean_Expr_letE___override(x_208, x_219, x_224, x_242, x_212);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_228, 0, x_247);
return x_228;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_228);
x_248 = lean_ctor_get(x_229, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_249 = x_229;
} else {
 lean_dec_ref(x_229);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
x_253 = l_Lean_Expr_letE___override(x_208, x_219, x_224, x_250, x_212);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
if (lean_is_scalar(x_249)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_249;
}
lean_ctor_set(x_255, 0, x_254);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
}
else
{
lean_dec(x_224);
lean_dec(x_219);
lean_dec(x_208);
return x_228;
}
}
}
else
{
lean_dec(x_219);
lean_dec_ref(x_215);
lean_dec_ref(x_211);
lean_dec(x_208);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_221;
}
}
}
else
{
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec(x_208);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_216;
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_257 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_64;
}
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_64);
x_259 = lean_ctor_get(x_1, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_260);
lean_dec_ref(x_1);
x_261 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_261);
lean_dec_ref(x_2);
x_262 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_260, x_261, x_70, x_69, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_dec(x_259);
return x_262;
}
else
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_262);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_262, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_263);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_263, 0);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = l_Lean_Expr_mdata___override(x_259, x_269);
lean_ctor_set(x_267, 0, x_270);
return x_262;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_267, 0);
x_272 = lean_ctor_get(x_267, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_267);
x_273 = l_Lean_Expr_mdata___override(x_259, x_271);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
lean_ctor_set(x_263, 0, x_274);
return x_262;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_275 = lean_ctor_get(x_263, 0);
lean_inc(x_275);
lean_dec(x_263);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
x_279 = l_Lean_Expr_mdata___override(x_259, x_276);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_277);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_262, 0, x_281);
return x_262;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_262);
x_282 = lean_ctor_get(x_263, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_283 = x_263;
} else {
 lean_dec_ref(x_263);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_286 = x_282;
} else {
 lean_dec_ref(x_282);
 x_286 = lean_box(0);
}
x_287 = l_Lean_Expr_mdata___override(x_259, x_284);
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_285);
if (lean_is_scalar(x_283)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_283;
}
lean_ctor_set(x_289, 0, x_288);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
}
}
else
{
lean_dec(x_259);
return x_262;
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_291 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_292 = lean_alloc_ctor(0, 1, 0);
} else {
 x_292 = x_64;
}
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
}
case 11:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_64);
x_293 = lean_ctor_get(x_1, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_1, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_295);
lean_dec_ref(x_1);
x_296 = lean_ctor_get(x_2, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_2, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_298);
lean_dec_ref(x_2);
x_299 = lean_name_eq(x_293, x_296);
lean_dec(x_296);
if (x_299 == 0)
{
lean_dec(x_297);
x_14 = x_295;
x_15 = x_77;
x_16 = lean_box(0);
x_17 = x_70;
x_18 = x_298;
x_19 = x_69;
x_20 = x_74;
x_21 = x_76;
x_22 = x_71;
x_23 = x_294;
x_24 = x_73;
x_25 = x_293;
x_26 = x_72;
x_27 = x_78;
x_28 = x_75;
x_29 = x_299;
goto block_61;
}
else
{
uint8_t x_300; 
x_300 = lean_nat_dec_eq(x_294, x_297);
lean_dec(x_297);
x_14 = x_295;
x_15 = x_77;
x_16 = lean_box(0);
x_17 = x_70;
x_18 = x_298;
x_19 = x_69;
x_20 = x_74;
x_21 = x_76;
x_22 = x_71;
x_23 = x_294;
x_24 = x_73;
x_25 = x_293;
x_26 = x_72;
x_27 = x_78;
x_28 = x_75;
x_29 = x_300;
goto block_61;
}
}
else
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_301 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_302 = x_64;
}
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
default: 
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_303 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_64;
}
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_530; 
x_377 = lean_ctor_get(x_66, 0);
x_378 = lean_ctor_get(x_66, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_66);
x_530 = lean_unbox(x_377);
lean_dec(x_377);
if (x_530 == 0)
{
lean_free_object(x_63);
x_379 = x_3;
x_380 = x_5;
x_381 = x_6;
x_382 = x_7;
x_383 = x_8;
x_384 = x_9;
x_385 = x_10;
x_386 = x_11;
x_387 = x_12;
x_388 = lean_box(0);
goto block_529;
}
else
{
uint8_t x_531; 
x_531 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_531 == 0)
{
uint8_t x_532; 
x_532 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_532 == 0)
{
lean_object* x_533; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_1);
x_533 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
lean_dec_ref(x_533);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_535 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
lean_dec_ref(x_535);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_537 = lean_grind_process_new_facts(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; 
lean_dec_ref(x_537);
x_538 = l_Lean_Meta_Grind_isEqv___redArg(x_534, x_536, x_5);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; uint8_t x_540; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
lean_dec_ref(x_538);
x_540 = lean_unbox(x_539);
lean_dec(x_539);
if (x_540 == 0)
{
lean_dec(x_536);
lean_dec(x_534);
lean_free_object(x_63);
x_379 = x_3;
x_380 = x_5;
x_381 = x_6;
x_382 = x_7;
x_383 = x_8;
x_384 = x_9;
x_385 = x_10;
x_386 = x_11;
x_387 = x_12;
x_388 = lean_box(0);
goto block_529;
}
else
{
lean_object* x_541; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_536);
lean_inc(x_534);
x_541 = l_Lean_Meta_Grind_hasSameType(x_534, x_536, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
lean_dec_ref(x_541);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_dec(x_536);
lean_dec(x_534);
lean_free_object(x_63);
x_379 = x_3;
x_380 = x_5;
x_381 = x_6;
x_382 = x_7;
x_383 = x_8;
x_384 = x_9;
x_385 = x_10;
x_386 = x_11;
x_387 = x_12;
x_388 = lean_box(0);
goto block_529;
}
else
{
lean_object* x_544; 
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc(x_534);
x_544 = lean_infer_type(x_534, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 x_546 = x_544;
} else {
 lean_dec_ref(x_544);
 x_546 = lean_box(0);
}
x_547 = lean_ctor_get(x_378, 0);
lean_inc_ref(x_547);
x_548 = lean_ctor_get(x_378, 1);
lean_inc_ref(x_548);
x_549 = lean_ctor_get(x_378, 2);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_378, 3);
lean_inc_ref(x_550);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_551 = x_378;
} else {
 lean_dec_ref(x_378);
 x_551 = lean_box(0);
}
x_552 = lean_array_get_size(x_548);
x_553 = lean_nat_add(x_552, x_3);
lean_dec(x_552);
x_554 = lean_array_push(x_548, x_545);
x_555 = lean_array_push(x_549, x_534);
x_556 = lean_array_push(x_550, x_536);
if (lean_is_scalar(x_551)) {
 x_557 = lean_alloc_ctor(0, 4, 0);
} else {
 x_557 = x_551;
}
lean_ctor_set(x_557, 0, x_547);
lean_ctor_set(x_557, 1, x_554);
lean_ctor_set(x_557, 2, x_555);
lean_ctor_set(x_557, 3, x_556);
x_558 = l_Lean_mkBVar(x_553);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
lean_ctor_set(x_63, 0, x_559);
if (lean_is_scalar(x_546)) {
 x_560 = lean_alloc_ctor(0, 1, 0);
} else {
 x_560 = x_546;
}
lean_ctor_set(x_560, 0, x_63);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_536);
lean_dec(x_534);
lean_dec(x_378);
lean_free_object(x_63);
x_561 = lean_ctor_get(x_544, 0);
lean_inc(x_561);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 x_562 = x_544;
} else {
 lean_dec_ref(x_544);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_561);
return x_563;
}
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_536);
lean_dec(x_534);
lean_dec(x_378);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_564 = lean_ctor_get(x_541, 0);
lean_inc(x_564);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 x_565 = x_541;
} else {
 lean_dec_ref(x_541);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(1, 1, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_564);
return x_566;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_536);
lean_dec(x_534);
lean_dec(x_378);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_567 = lean_ctor_get(x_538, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 x_568 = x_538;
} else {
 lean_dec_ref(x_538);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 1, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_567);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_536);
lean_dec(x_534);
lean_dec(x_378);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_570 = lean_ctor_get(x_537, 0);
lean_inc(x_570);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 x_571 = x_537;
} else {
 lean_dec_ref(x_537);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(1, 1, 0);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_570);
return x_572;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_534);
lean_dec(x_378);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_573 = lean_ctor_get(x_535, 0);
lean_inc(x_573);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 x_574 = x_535;
} else {
 lean_dec_ref(x_535);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(1, 1, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_573);
return x_575;
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_378);
lean_free_object(x_63);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_576 = lean_ctor_get(x_533, 0);
lean_inc(x_576);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_577 = x_533;
} else {
 lean_dec_ref(x_533);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(1, 1, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_576);
return x_578;
}
}
else
{
lean_free_object(x_63);
x_379 = x_3;
x_380 = x_5;
x_381 = x_6;
x_382 = x_7;
x_383 = x_8;
x_384 = x_9;
x_385 = x_10;
x_386 = x_11;
x_387 = x_12;
x_388 = lean_box(0);
goto block_529;
}
}
else
{
lean_free_object(x_63);
x_379 = x_3;
x_380 = x_5;
x_381 = x_6;
x_382 = x_7;
x_383 = x_8;
x_384 = x_9;
x_385 = x_10;
x_386 = x_11;
x_387 = x_12;
x_388 = lean_box(0);
goto block_529;
}
}
block_529:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_64);
x_389 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_389);
x_390 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_390);
lean_dec_ref(x_1);
x_391 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_391);
x_392 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_392);
lean_dec_ref(x_2);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc(x_385);
lean_inc_ref(x_384);
lean_inc(x_383);
lean_inc_ref(x_382);
lean_inc(x_381);
lean_inc(x_380);
x_393 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_389, x_391, x_379, x_378, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
if (lean_obj_tag(x_394) == 0)
{
lean_dec_ref(x_392);
lean_dec_ref(x_390);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_393;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec_ref(x_393);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_390, x_392, x_379, x_397, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_dec(x_396);
return x_398;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_400 = x_398;
} else {
 lean_dec_ref(x_398);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_402 = x_399;
} else {
 lean_dec_ref(x_399);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_401, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_405 = x_401;
} else {
 lean_dec_ref(x_401);
 x_405 = lean_box(0);
}
x_406 = l_Lean_Expr_app___override(x_396, x_403);
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_405;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_404);
if (lean_is_scalar(x_402)) {
 x_408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_408 = x_402;
}
lean_ctor_set(x_408, 0, x_407);
if (lean_is_scalar(x_400)) {
 x_409 = lean_alloc_ctor(0, 1, 0);
} else {
 x_409 = x_400;
}
lean_ctor_set(x_409, 0, x_408);
return x_409;
}
}
else
{
lean_dec(x_396);
return x_398;
}
}
}
else
{
lean_dec_ref(x_392);
lean_dec_ref(x_390);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_393;
}
}
else
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_410 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_411 = lean_alloc_ctor(0, 1, 0);
} else {
 x_411 = x_64;
}
lean_ctor_set(x_411, 0, x_410);
return x_411;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_64);
x_412 = lean_ctor_get(x_1, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_413);
x_414 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_414);
x_415 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_416 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_417);
lean_dec_ref(x_2);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc(x_385);
lean_inc_ref(x_384);
lean_inc(x_383);
lean_inc_ref(x_382);
lean_inc(x_381);
lean_inc(x_380);
x_418 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_413, x_416, x_379, x_378, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
if (lean_obj_tag(x_419) == 0)
{
lean_dec_ref(x_417);
lean_dec_ref(x_414);
lean_dec(x_412);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_418;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec_ref(x_418);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_unsigned_to_nat(1u);
x_424 = lean_nat_add(x_379, x_423);
x_425 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_414, x_417, x_424, x_422, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
lean_dec(x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_dec(x_421);
lean_dec(x_412);
return x_425;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_427 = x_425;
} else {
 lean_dec_ref(x_425);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_429 = x_426;
} else {
 lean_dec_ref(x_426);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_432 = x_428;
} else {
 lean_dec_ref(x_428);
 x_432 = lean_box(0);
}
x_433 = l_Lean_mkLambda(x_412, x_415, x_421, x_430);
if (lean_is_scalar(x_432)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_432;
}
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_431);
if (lean_is_scalar(x_429)) {
 x_435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_435 = x_429;
}
lean_ctor_set(x_435, 0, x_434);
if (lean_is_scalar(x_427)) {
 x_436 = lean_alloc_ctor(0, 1, 0);
} else {
 x_436 = x_427;
}
lean_ctor_set(x_436, 0, x_435);
return x_436;
}
}
else
{
lean_dec(x_421);
lean_dec(x_412);
return x_425;
}
}
}
else
{
lean_dec_ref(x_417);
lean_dec_ref(x_414);
lean_dec(x_412);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_418;
}
}
else
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_437 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_438 = lean_alloc_ctor(0, 1, 0);
} else {
 x_438 = x_64;
}
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_64);
x_439 = lean_ctor_get(x_1, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_440);
x_441 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_441);
x_442 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_443 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_443);
x_444 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_444);
lean_dec_ref(x_2);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc(x_385);
lean_inc_ref(x_384);
lean_inc(x_383);
lean_inc_ref(x_382);
lean_inc(x_381);
lean_inc(x_380);
x_445 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_440, x_443, x_379, x_378, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_dec_ref(x_444);
lean_dec_ref(x_441);
lean_dec(x_439);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_445;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec_ref(x_445);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_unsigned_to_nat(1u);
x_451 = lean_nat_add(x_379, x_450);
x_452 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_441, x_444, x_451, x_449, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
lean_dec(x_451);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
if (lean_obj_tag(x_453) == 0)
{
lean_dec(x_448);
lean_dec(x_439);
return x_452;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_455, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_455, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_459 = x_455;
} else {
 lean_dec_ref(x_455);
 x_459 = lean_box(0);
}
x_460 = l_Lean_mkForall(x_439, x_442, x_448, x_457);
if (lean_is_scalar(x_459)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_459;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_458);
if (lean_is_scalar(x_456)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_456;
}
lean_ctor_set(x_462, 0, x_461);
if (lean_is_scalar(x_454)) {
 x_463 = lean_alloc_ctor(0, 1, 0);
} else {
 x_463 = x_454;
}
lean_ctor_set(x_463, 0, x_462);
return x_463;
}
}
else
{
lean_dec(x_448);
lean_dec(x_439);
return x_452;
}
}
}
else
{
lean_dec_ref(x_444);
lean_dec_ref(x_441);
lean_dec(x_439);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_445;
}
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_464 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_465 = lean_alloc_ctor(0, 1, 0);
} else {
 x_465 = x_64;
}
lean_ctor_set(x_465, 0, x_464);
return x_465;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_64);
x_466 = lean_ctor_get(x_1, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_469);
x_470 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_473);
lean_dec_ref(x_2);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc(x_385);
lean_inc_ref(x_384);
lean_inc(x_383);
lean_inc_ref(x_382);
lean_inc(x_381);
lean_inc(x_380);
x_474 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_467, x_471, x_379, x_378, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_dec_ref(x_473);
lean_dec_ref(x_472);
lean_dec_ref(x_469);
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_474;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec_ref(x_474);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
lean_dec_ref(x_475);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc(x_385);
lean_inc_ref(x_384);
lean_inc(x_383);
lean_inc_ref(x_382);
lean_inc(x_381);
lean_inc(x_380);
x_479 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_468, x_472, x_379, x_478, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
if (lean_obj_tag(x_480) == 0)
{
lean_dec(x_477);
lean_dec_ref(x_473);
lean_dec_ref(x_469);
lean_dec(x_466);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_479;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec_ref(x_479);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
lean_dec_ref(x_480);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_unsigned_to_nat(1u);
x_485 = lean_nat_add(x_379, x_484);
x_486 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_469, x_473, x_485, x_483, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
lean_dec(x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_466);
return x_486;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_487, 0);
lean_inc(x_489);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 x_490 = x_487;
} else {
 lean_dec_ref(x_487);
 x_490 = lean_box(0);
}
x_491 = lean_ctor_get(x_489, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_493 = x_489;
} else {
 lean_dec_ref(x_489);
 x_493 = lean_box(0);
}
x_494 = l_Lean_Expr_letE___override(x_466, x_477, x_482, x_491, x_470);
if (lean_is_scalar(x_493)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_493;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_492);
if (lean_is_scalar(x_490)) {
 x_496 = lean_alloc_ctor(1, 1, 0);
} else {
 x_496 = x_490;
}
lean_ctor_set(x_496, 0, x_495);
if (lean_is_scalar(x_488)) {
 x_497 = lean_alloc_ctor(0, 1, 0);
} else {
 x_497 = x_488;
}
lean_ctor_set(x_497, 0, x_496);
return x_497;
}
}
else
{
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_466);
return x_486;
}
}
}
else
{
lean_dec(x_477);
lean_dec_ref(x_473);
lean_dec_ref(x_469);
lean_dec(x_466);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_479;
}
}
}
else
{
lean_dec_ref(x_473);
lean_dec_ref(x_472);
lean_dec_ref(x_469);
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
return x_474;
}
}
else
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_498 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_499 = lean_alloc_ctor(0, 1, 0);
} else {
 x_499 = x_64;
}
lean_ctor_set(x_499, 0, x_498);
return x_499;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_64);
x_500 = lean_ctor_get(x_1, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_501);
lean_dec_ref(x_1);
x_502 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_502);
lean_dec_ref(x_2);
x_503 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_501, x_502, x_379, x_378, x_380, x_381, x_382, x_383, x_384, x_385, x_386, x_387);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
if (lean_obj_tag(x_504) == 0)
{
lean_dec(x_500);
return x_503;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 x_505 = x_503;
} else {
 lean_dec_ref(x_503);
 x_505 = lean_box(0);
}
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_507 = x_504;
} else {
 lean_dec_ref(x_504);
 x_507 = lean_box(0);
}
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_510 = x_506;
} else {
 lean_dec_ref(x_506);
 x_510 = lean_box(0);
}
x_511 = l_Lean_Expr_mdata___override(x_500, x_508);
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_510;
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_509);
if (lean_is_scalar(x_507)) {
 x_513 = lean_alloc_ctor(1, 1, 0);
} else {
 x_513 = x_507;
}
lean_ctor_set(x_513, 0, x_512);
if (lean_is_scalar(x_505)) {
 x_514 = lean_alloc_ctor(0, 1, 0);
} else {
 x_514 = x_505;
}
lean_ctor_set(x_514, 0, x_513);
return x_514;
}
}
else
{
lean_dec(x_500);
return x_503;
}
}
else
{
lean_object* x_515; lean_object* x_516; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_515 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_516 = lean_alloc_ctor(0, 1, 0);
} else {
 x_516 = x_64;
}
lean_ctor_set(x_516, 0, x_515);
return x_516;
}
}
case 11:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
lean_dec(x_64);
x_517 = lean_ctor_get(x_1, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_1, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_519);
lean_dec_ref(x_1);
x_520 = lean_ctor_get(x_2, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_2, 1);
lean_inc(x_521);
x_522 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_522);
lean_dec_ref(x_2);
x_523 = lean_name_eq(x_517, x_520);
lean_dec(x_520);
if (x_523 == 0)
{
lean_dec(x_521);
x_14 = x_519;
x_15 = x_386;
x_16 = lean_box(0);
x_17 = x_379;
x_18 = x_522;
x_19 = x_378;
x_20 = x_383;
x_21 = x_385;
x_22 = x_380;
x_23 = x_518;
x_24 = x_382;
x_25 = x_517;
x_26 = x_381;
x_27 = x_387;
x_28 = x_384;
x_29 = x_523;
goto block_61;
}
else
{
uint8_t x_524; 
x_524 = lean_nat_dec_eq(x_518, x_521);
lean_dec(x_521);
x_14 = x_519;
x_15 = x_386;
x_16 = lean_box(0);
x_17 = x_379;
x_18 = x_522;
x_19 = x_378;
x_20 = x_383;
x_21 = x_385;
x_22 = x_380;
x_23 = x_518;
x_24 = x_382;
x_25 = x_517;
x_26 = x_381;
x_27 = x_387;
x_28 = x_384;
x_29 = x_524;
goto block_61;
}
}
else
{
lean_object* x_525; lean_object* x_526; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_525 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_526 = lean_alloc_ctor(0, 1, 0);
} else {
 x_526 = x_64;
}
lean_ctor_set(x_526, 0, x_525);
return x_526;
}
}
default: 
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_527 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_528 = lean_alloc_ctor(0, 1, 0);
} else {
 x_528 = x_64;
}
lean_ctor_set(x_528, 0, x_527);
return x_528;
}
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_734; 
x_579 = lean_ctor_get(x_63, 0);
lean_inc(x_579);
lean_dec(x_63);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_582 = x_579;
} else {
 lean_dec_ref(x_579);
 x_582 = lean_box(0);
}
x_734 = lean_unbox(x_580);
lean_dec(x_580);
if (x_734 == 0)
{
lean_dec(x_582);
x_583 = x_3;
x_584 = x_5;
x_585 = x_6;
x_586 = x_7;
x_587 = x_8;
x_588 = x_9;
x_589 = x_10;
x_590 = x_11;
x_591 = x_12;
x_592 = lean_box(0);
goto block_733;
}
else
{
uint8_t x_735; 
x_735 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_735 == 0)
{
uint8_t x_736; 
x_736 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_736 == 0)
{
lean_object* x_737; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_1);
x_737 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; 
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
lean_dec_ref(x_737);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_739 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
lean_dec_ref(x_739);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_741 = lean_grind_process_new_facts(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; 
lean_dec_ref(x_741);
x_742 = l_Lean_Meta_Grind_isEqv___redArg(x_738, x_740, x_5);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; uint8_t x_744; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
lean_dec_ref(x_742);
x_744 = lean_unbox(x_743);
lean_dec(x_743);
if (x_744 == 0)
{
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_582);
x_583 = x_3;
x_584 = x_5;
x_585 = x_6;
x_586 = x_7;
x_587 = x_8;
x_588 = x_9;
x_589 = x_10;
x_590 = x_11;
x_591 = x_12;
x_592 = lean_box(0);
goto block_733;
}
else
{
lean_object* x_745; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_740);
lean_inc(x_738);
x_745 = l_Lean_Meta_Grind_hasSameType(x_738, x_740, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; uint8_t x_747; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
lean_dec_ref(x_745);
x_747 = lean_unbox(x_746);
lean_dec(x_746);
if (x_747 == 0)
{
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_582);
x_583 = x_3;
x_584 = x_5;
x_585 = x_6;
x_586 = x_7;
x_587 = x_8;
x_588 = x_9;
x_589 = x_10;
x_590 = x_11;
x_591 = x_12;
x_592 = lean_box(0);
goto block_733;
}
else
{
lean_object* x_748; 
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc(x_738);
x_748 = lean_infer_type(x_738, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 x_750 = x_748;
} else {
 lean_dec_ref(x_748);
 x_750 = lean_box(0);
}
x_751 = lean_ctor_get(x_581, 0);
lean_inc_ref(x_751);
x_752 = lean_ctor_get(x_581, 1);
lean_inc_ref(x_752);
x_753 = lean_ctor_get(x_581, 2);
lean_inc_ref(x_753);
x_754 = lean_ctor_get(x_581, 3);
lean_inc_ref(x_754);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 lean_ctor_release(x_581, 2);
 lean_ctor_release(x_581, 3);
 x_755 = x_581;
} else {
 lean_dec_ref(x_581);
 x_755 = lean_box(0);
}
x_756 = lean_array_get_size(x_752);
x_757 = lean_nat_add(x_756, x_3);
lean_dec(x_756);
x_758 = lean_array_push(x_752, x_749);
x_759 = lean_array_push(x_753, x_738);
x_760 = lean_array_push(x_754, x_740);
if (lean_is_scalar(x_755)) {
 x_761 = lean_alloc_ctor(0, 4, 0);
} else {
 x_761 = x_755;
}
lean_ctor_set(x_761, 0, x_751);
lean_ctor_set(x_761, 1, x_758);
lean_ctor_set(x_761, 2, x_759);
lean_ctor_set(x_761, 3, x_760);
x_762 = l_Lean_mkBVar(x_757);
if (lean_is_scalar(x_582)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_582;
}
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_761);
x_764 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_764, 0, x_763);
if (lean_is_scalar(x_750)) {
 x_765 = lean_alloc_ctor(0, 1, 0);
} else {
 x_765 = x_750;
}
lean_ctor_set(x_765, 0, x_764);
return x_765;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_582);
lean_dec(x_581);
x_766 = lean_ctor_get(x_748, 0);
lean_inc(x_766);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 x_767 = x_748;
} else {
 lean_dec_ref(x_748);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 1, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_766);
return x_768;
}
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_769 = lean_ctor_get(x_745, 0);
lean_inc(x_769);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 x_770 = x_745;
} else {
 lean_dec_ref(x_745);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 1, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_769);
return x_771;
}
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_772 = lean_ctor_get(x_742, 0);
lean_inc(x_772);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 x_773 = x_742;
} else {
 lean_dec_ref(x_742);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_772);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_775 = lean_ctor_get(x_741, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 x_776 = x_741;
} else {
 lean_dec_ref(x_741);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(1, 1, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_775);
return x_777;
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_738);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_778 = lean_ctor_get(x_739, 0);
lean_inc(x_778);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 x_779 = x_739;
} else {
 lean_dec_ref(x_739);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 1, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_778);
return x_780;
}
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_781 = lean_ctor_get(x_737, 0);
lean_inc(x_781);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 x_782 = x_737;
} else {
 lean_dec_ref(x_737);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 1, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_781);
return x_783;
}
}
else
{
lean_dec(x_582);
x_583 = x_3;
x_584 = x_5;
x_585 = x_6;
x_586 = x_7;
x_587 = x_8;
x_588 = x_9;
x_589 = x_10;
x_590 = x_11;
x_591 = x_12;
x_592 = lean_box(0);
goto block_733;
}
}
else
{
lean_dec(x_582);
x_583 = x_3;
x_584 = x_5;
x_585 = x_6;
x_586 = x_7;
x_587 = x_8;
x_588 = x_9;
x_589 = x_10;
x_590 = x_11;
x_591 = x_12;
x_592 = lean_box(0);
goto block_733;
}
}
block_733:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_64);
x_593 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_593);
x_594 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_594);
lean_dec_ref(x_1);
x_595 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_595);
x_596 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_596);
lean_dec_ref(x_2);
lean_inc(x_591);
lean_inc_ref(x_590);
lean_inc(x_589);
lean_inc_ref(x_588);
lean_inc(x_587);
lean_inc_ref(x_586);
lean_inc(x_585);
lean_inc(x_584);
x_597 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_593, x_595, x_583, x_581, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
if (lean_obj_tag(x_598) == 0)
{
lean_dec_ref(x_596);
lean_dec_ref(x_594);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_597;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec_ref(x_597);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
lean_dec_ref(x_598);
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_594, x_596, x_583, x_601, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_obj_tag(x_603) == 0)
{
lean_dec(x_600);
return x_602;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 x_604 = x_602;
} else {
 lean_dec_ref(x_602);
 x_604 = lean_box(0);
}
x_605 = lean_ctor_get(x_603, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_606 = x_603;
} else {
 lean_dec_ref(x_603);
 x_606 = lean_box(0);
}
x_607 = lean_ctor_get(x_605, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_605, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_609 = x_605;
} else {
 lean_dec_ref(x_605);
 x_609 = lean_box(0);
}
x_610 = l_Lean_Expr_app___override(x_600, x_607);
if (lean_is_scalar(x_609)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_609;
}
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_608);
if (lean_is_scalar(x_606)) {
 x_612 = lean_alloc_ctor(1, 1, 0);
} else {
 x_612 = x_606;
}
lean_ctor_set(x_612, 0, x_611);
if (lean_is_scalar(x_604)) {
 x_613 = lean_alloc_ctor(0, 1, 0);
} else {
 x_613 = x_604;
}
lean_ctor_set(x_613, 0, x_612);
return x_613;
}
}
else
{
lean_dec(x_600);
return x_602;
}
}
}
else
{
lean_dec_ref(x_596);
lean_dec_ref(x_594);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_597;
}
}
else
{
lean_object* x_614; lean_object* x_615; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_614 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_615 = lean_alloc_ctor(0, 1, 0);
} else {
 x_615 = x_64;
}
lean_ctor_set(x_615, 0, x_614);
return x_615;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_64);
x_616 = lean_ctor_get(x_1, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_617);
x_618 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_618);
x_619 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_620 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_620);
x_621 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_621);
lean_dec_ref(x_2);
lean_inc(x_591);
lean_inc_ref(x_590);
lean_inc(x_589);
lean_inc_ref(x_588);
lean_inc(x_587);
lean_inc_ref(x_586);
lean_inc(x_585);
lean_inc(x_584);
x_622 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_617, x_620, x_583, x_581, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
if (lean_obj_tag(x_623) == 0)
{
lean_dec_ref(x_621);
lean_dec_ref(x_618);
lean_dec(x_616);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_622;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec_ref(x_622);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
lean_dec_ref(x_623);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = lean_unsigned_to_nat(1u);
x_628 = lean_nat_add(x_583, x_627);
x_629 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_618, x_621, x_628, x_626, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
lean_dec(x_628);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
if (lean_obj_tag(x_630) == 0)
{
lean_dec(x_625);
lean_dec(x_616);
return x_629;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 x_631 = x_629;
} else {
 lean_dec_ref(x_629);
 x_631 = lean_box(0);
}
x_632 = lean_ctor_get(x_630, 0);
lean_inc(x_632);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 x_633 = x_630;
} else {
 lean_dec_ref(x_630);
 x_633 = lean_box(0);
}
x_634 = lean_ctor_get(x_632, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_636 = x_632;
} else {
 lean_dec_ref(x_632);
 x_636 = lean_box(0);
}
x_637 = l_Lean_mkLambda(x_616, x_619, x_625, x_634);
if (lean_is_scalar(x_636)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_636;
}
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_635);
if (lean_is_scalar(x_633)) {
 x_639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_639 = x_633;
}
lean_ctor_set(x_639, 0, x_638);
if (lean_is_scalar(x_631)) {
 x_640 = lean_alloc_ctor(0, 1, 0);
} else {
 x_640 = x_631;
}
lean_ctor_set(x_640, 0, x_639);
return x_640;
}
}
else
{
lean_dec(x_625);
lean_dec(x_616);
return x_629;
}
}
}
else
{
lean_dec_ref(x_621);
lean_dec_ref(x_618);
lean_dec(x_616);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_622;
}
}
else
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_641 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_642 = lean_alloc_ctor(0, 1, 0);
} else {
 x_642 = x_64;
}
lean_ctor_set(x_642, 0, x_641);
return x_642;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_64);
x_643 = lean_ctor_get(x_1, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_644);
x_645 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_645);
x_646 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_647 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_647);
x_648 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_648);
lean_dec_ref(x_2);
lean_inc(x_591);
lean_inc_ref(x_590);
lean_inc(x_589);
lean_inc_ref(x_588);
lean_inc(x_587);
lean_inc_ref(x_586);
lean_inc(x_585);
lean_inc(x_584);
x_649 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_644, x_647, x_583, x_581, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
if (lean_obj_tag(x_650) == 0)
{
lean_dec_ref(x_648);
lean_dec_ref(x_645);
lean_dec(x_643);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_649;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec_ref(x_649);
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
lean_dec_ref(x_650);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_unsigned_to_nat(1u);
x_655 = lean_nat_add(x_583, x_654);
x_656 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_645, x_648, x_655, x_653, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
lean_dec(x_655);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
if (lean_obj_tag(x_657) == 0)
{
lean_dec(x_652);
lean_dec(x_643);
return x_656;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 x_658 = x_656;
} else {
 lean_dec_ref(x_656);
 x_658 = lean_box(0);
}
x_659 = lean_ctor_get(x_657, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 x_660 = x_657;
} else {
 lean_dec_ref(x_657);
 x_660 = lean_box(0);
}
x_661 = lean_ctor_get(x_659, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_663 = x_659;
} else {
 lean_dec_ref(x_659);
 x_663 = lean_box(0);
}
x_664 = l_Lean_mkForall(x_643, x_646, x_652, x_661);
if (lean_is_scalar(x_663)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_663;
}
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_662);
if (lean_is_scalar(x_660)) {
 x_666 = lean_alloc_ctor(1, 1, 0);
} else {
 x_666 = x_660;
}
lean_ctor_set(x_666, 0, x_665);
if (lean_is_scalar(x_658)) {
 x_667 = lean_alloc_ctor(0, 1, 0);
} else {
 x_667 = x_658;
}
lean_ctor_set(x_667, 0, x_666);
return x_667;
}
}
else
{
lean_dec(x_652);
lean_dec(x_643);
return x_656;
}
}
}
else
{
lean_dec_ref(x_648);
lean_dec_ref(x_645);
lean_dec(x_643);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_649;
}
}
else
{
lean_object* x_668; lean_object* x_669; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_668 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_669 = lean_alloc_ctor(0, 1, 0);
} else {
 x_669 = x_64;
}
lean_ctor_set(x_669, 0, x_668);
return x_669;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_64);
x_670 = lean_ctor_get(x_1, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_671);
x_672 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_672);
x_673 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_673);
x_674 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec_ref(x_1);
x_675 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_675);
x_676 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_676);
x_677 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_677);
lean_dec_ref(x_2);
lean_inc(x_591);
lean_inc_ref(x_590);
lean_inc(x_589);
lean_inc_ref(x_588);
lean_inc(x_587);
lean_inc_ref(x_586);
lean_inc(x_585);
lean_inc(x_584);
x_678 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_671, x_675, x_583, x_581, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
if (lean_obj_tag(x_679) == 0)
{
lean_dec_ref(x_677);
lean_dec_ref(x_676);
lean_dec_ref(x_673);
lean_dec_ref(x_672);
lean_dec(x_670);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_678;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec_ref(x_678);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
lean_dec_ref(x_679);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
lean_inc(x_591);
lean_inc_ref(x_590);
lean_inc(x_589);
lean_inc_ref(x_588);
lean_inc(x_587);
lean_inc_ref(x_586);
lean_inc(x_585);
lean_inc(x_584);
x_683 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_672, x_676, x_583, x_682, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
if (lean_obj_tag(x_684) == 0)
{
lean_dec(x_681);
lean_dec_ref(x_677);
lean_dec_ref(x_673);
lean_dec(x_670);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_683;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec_ref(x_683);
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
lean_dec_ref(x_684);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = lean_unsigned_to_nat(1u);
x_689 = lean_nat_add(x_583, x_688);
x_690 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_673, x_677, x_689, x_687, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
lean_dec(x_689);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
if (lean_obj_tag(x_691) == 0)
{
lean_dec(x_686);
lean_dec(x_681);
lean_dec(x_670);
return x_690;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 x_692 = x_690;
} else {
 lean_dec_ref(x_690);
 x_692 = lean_box(0);
}
x_693 = lean_ctor_get(x_691, 0);
lean_inc(x_693);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 x_694 = x_691;
} else {
 lean_dec_ref(x_691);
 x_694 = lean_box(0);
}
x_695 = lean_ctor_get(x_693, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_693, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_697 = x_693;
} else {
 lean_dec_ref(x_693);
 x_697 = lean_box(0);
}
x_698 = l_Lean_Expr_letE___override(x_670, x_681, x_686, x_695, x_674);
if (lean_is_scalar(x_697)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_697;
}
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_696);
if (lean_is_scalar(x_694)) {
 x_700 = lean_alloc_ctor(1, 1, 0);
} else {
 x_700 = x_694;
}
lean_ctor_set(x_700, 0, x_699);
if (lean_is_scalar(x_692)) {
 x_701 = lean_alloc_ctor(0, 1, 0);
} else {
 x_701 = x_692;
}
lean_ctor_set(x_701, 0, x_700);
return x_701;
}
}
else
{
lean_dec(x_686);
lean_dec(x_681);
lean_dec(x_670);
return x_690;
}
}
}
else
{
lean_dec(x_681);
lean_dec_ref(x_677);
lean_dec_ref(x_673);
lean_dec(x_670);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_683;
}
}
}
else
{
lean_dec_ref(x_677);
lean_dec_ref(x_676);
lean_dec_ref(x_673);
lean_dec_ref(x_672);
lean_dec(x_670);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
return x_678;
}
}
else
{
lean_object* x_702; lean_object* x_703; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_702 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_703 = lean_alloc_ctor(0, 1, 0);
} else {
 x_703 = x_64;
}
lean_ctor_set(x_703, 0, x_702);
return x_703;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_64);
x_704 = lean_ctor_get(x_1, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_705);
lean_dec_ref(x_1);
x_706 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_706);
lean_dec_ref(x_2);
x_707 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_705, x_706, x_583, x_581, x_584, x_585, x_586, x_587, x_588, x_589, x_590, x_591);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
if (lean_obj_tag(x_708) == 0)
{
lean_dec(x_704);
return x_707;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 x_709 = x_707;
} else {
 lean_dec_ref(x_707);
 x_709 = lean_box(0);
}
x_710 = lean_ctor_get(x_708, 0);
lean_inc(x_710);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 x_711 = x_708;
} else {
 lean_dec_ref(x_708);
 x_711 = lean_box(0);
}
x_712 = lean_ctor_get(x_710, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_710, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_714 = x_710;
} else {
 lean_dec_ref(x_710);
 x_714 = lean_box(0);
}
x_715 = l_Lean_Expr_mdata___override(x_704, x_712);
if (lean_is_scalar(x_714)) {
 x_716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_716 = x_714;
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_713);
if (lean_is_scalar(x_711)) {
 x_717 = lean_alloc_ctor(1, 1, 0);
} else {
 x_717 = x_711;
}
lean_ctor_set(x_717, 0, x_716);
if (lean_is_scalar(x_709)) {
 x_718 = lean_alloc_ctor(0, 1, 0);
} else {
 x_718 = x_709;
}
lean_ctor_set(x_718, 0, x_717);
return x_718;
}
}
else
{
lean_dec(x_704);
return x_707;
}
}
else
{
lean_object* x_719; lean_object* x_720; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_719 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_720 = lean_alloc_ctor(0, 1, 0);
} else {
 x_720 = x_64;
}
lean_ctor_set(x_720, 0, x_719);
return x_720;
}
}
case 11:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
lean_dec(x_64);
x_721 = lean_ctor_get(x_1, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_1, 1);
lean_inc(x_722);
x_723 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_723);
lean_dec_ref(x_1);
x_724 = lean_ctor_get(x_2, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_2, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_726);
lean_dec_ref(x_2);
x_727 = lean_name_eq(x_721, x_724);
lean_dec(x_724);
if (x_727 == 0)
{
lean_dec(x_725);
x_14 = x_723;
x_15 = x_590;
x_16 = lean_box(0);
x_17 = x_583;
x_18 = x_726;
x_19 = x_581;
x_20 = x_587;
x_21 = x_589;
x_22 = x_584;
x_23 = x_722;
x_24 = x_586;
x_25 = x_721;
x_26 = x_585;
x_27 = x_591;
x_28 = x_588;
x_29 = x_727;
goto block_61;
}
else
{
uint8_t x_728; 
x_728 = lean_nat_dec_eq(x_722, x_725);
lean_dec(x_725);
x_14 = x_723;
x_15 = x_590;
x_16 = lean_box(0);
x_17 = x_583;
x_18 = x_726;
x_19 = x_581;
x_20 = x_587;
x_21 = x_589;
x_22 = x_584;
x_23 = x_722;
x_24 = x_586;
x_25 = x_721;
x_26 = x_585;
x_27 = x_591;
x_28 = x_588;
x_29 = x_728;
goto block_61;
}
}
else
{
lean_object* x_729; lean_object* x_730; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_729 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_730 = lean_alloc_ctor(0, 1, 0);
} else {
 x_730 = x_64;
}
lean_ctor_set(x_730, 0, x_729);
return x_730;
}
}
default: 
{
lean_object* x_731; lean_object* x_732; 
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_588);
lean_dec(x_587);
lean_dec_ref(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_581);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_731 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_732 = lean_alloc_ctor(0, 1, 0);
} else {
 x_732 = x_64;
}
lean_ctor_set(x_732, 0, x_731);
return x_732;
}
}
}
}
block_61:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_14, x_18, x_17, x_19, x_22, x_26, x_24, x_20, x_28, x_21, x_15, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_25);
lean_dec(x_23);
return x_32;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Expr_proj___override(x_25, x_23, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = l_Lean_Expr_proj___override(x_25, x_23, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_33, 0, x_44);
return x_32;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Expr_proj___override(x_25, x_23, x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_32, 0, x_51);
return x_32;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_32);
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_53 = x_33;
} else {
 lean_dec_ref(x_33);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Expr_proj___override(x_25, x_23, x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_23);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_expr_eqv(x_11, x_13);
if (x_15 == 0)
{
x_7 = x_15;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_12, x_14);
x_7 = x_16;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_3);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = l_Lean_Expr_hash(x_5);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg(x_2, x_21);
lean_dec(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_expr_eqv(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = lean_expr_eqv(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_hash(x_6);
x_10 = l_Lean_Expr_hash(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_array_get_size(x_1);
x_32 = l_Lean_Expr_hash(x_29);
x_33 = l_Lean_Expr_hash(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3_spec__3___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_expr_eqv(x_13, x_15);
if (x_17 == 0)
{
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_expr_eqv(x_14, x_16);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_6);
x_10 = l_Lean_Expr_hash(x_7);
x_11 = l_Lean_Expr_hash(x_8);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_array_uset(x_6, x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(x_29);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_box(0);
x_38 = lean_array_uset(x_6, x_23, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6___redArg(x_2, x_3, x_24);
x_40 = lean_array_uset(x_38, x_23, x_39);
lean_ctor_set(x_1, 1, x_40);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_array_get_size(x_42);
x_46 = l_Lean_Expr_hash(x_43);
x_47 = l_Lean_Expr_hash(x_44);
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_42, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_41, x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_array_uset(x_42, x_59, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_63, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_42, x_59, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__6___redArg(x_2, x_3, x_60);
x_78 = lean_array_uset(x_76, x_59, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg(x_15, x_16);
if (lean_obj_tag(x_17) == 1)
{
uint8_t x_18; 
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_17, 0, x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_17);
x_26 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_16);
return x_26;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_37 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(x_36, x_16, x_35);
lean_ctor_set(x_33, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
x_41 = lean_ctor_get(x_33, 2);
x_42 = lean_ctor_get(x_33, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
lean_inc(x_38);
x_43 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(x_39, x_16, x_38);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_31, 1, x_44);
return x_26;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_31, 1);
x_46 = lean_ctor_get(x_31, 0);
lean_inc(x_45);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_45, 2);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_45, 3);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
lean_inc(x_46);
x_52 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(x_47, x_16, x_46);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 4, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_27, 0, x_54);
return x_26;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_27, 0);
lean_inc(x_55);
lean_dec(x_27);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_56, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_56, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_56, 3);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
lean_inc(x_57);
x_64 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(x_59, x_16, x_57);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 4, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
if (lean_is_scalar(x_58)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_58;
}
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_26, 0, x_67);
return x_26;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_26);
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_69 = x_27;
} else {
 lean_dec_ref(x_27);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_70, 2);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_70, 3);
lean_inc_ref(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
lean_inc(x_71);
x_78 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(x_73, x_16, x_71);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_69)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_69;
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_dec_ref(x_16);
return x_26;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_4);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_shareCommon___redArg(x_1, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_Grind_shareCommon___redArg(x_2, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6;
x_18 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(x_13, x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 1)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_28);
lean_dec(x_24);
x_29 = l_Array_isEmpty___redArg(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(x_26, x_25);
lean_dec_ref(x_26);
lean_inc_ref(x_30);
x_31 = l_Lean_mkAppN(x_30, x_27);
lean_dec_ref(x_27);
x_32 = l_Lean_mkAppN(x_30, x_28);
lean_dec_ref(x_28);
lean_ctor_set(x_22, 1, x_32);
lean_ctor_set(x_22, 0, x_31);
return x_18;
}
else
{
lean_object* x_33; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_free_object(x_22);
lean_dec(x_25);
lean_free_object(x_20);
x_33 = lean_box(0);
lean_ctor_set(x_18, 0, x_33);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_22, 1);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_34, 3);
lean_inc_ref(x_38);
lean_dec(x_34);
x_39 = l_Array_isEmpty___redArg(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(x_36, x_35);
lean_dec_ref(x_36);
lean_inc_ref(x_40);
x_41 = l_Lean_mkAppN(x_40, x_37);
lean_dec_ref(x_37);
x_42 = l_Lean_mkAppN(x_40, x_38);
lean_dec_ref(x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_20, 0, x_43);
return x_18;
}
else
{
lean_object* x_44; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_free_object(x_20);
x_44 = lean_box(0);
lean_ctor_set(x_18, 0, x_44);
return x_18;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_20, 0);
lean_inc(x_45);
lean_dec(x_20);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_46, 3);
lean_inc_ref(x_51);
lean_dec(x_46);
x_52 = l_Array_isEmpty___redArg(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(x_49, x_47);
lean_dec_ref(x_49);
lean_inc_ref(x_53);
x_54 = l_Lean_mkAppN(x_53, x_50);
lean_dec_ref(x_50);
x_55 = l_Lean_mkAppN(x_53, x_51);
lean_dec_ref(x_51);
if (lean_is_scalar(x_48)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_48;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_18, 0, x_57);
return x_18;
}
else
{
lean_object* x_58; 
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec(x_47);
x_58 = lean_box(0);
lean_ctor_set(x_18, 0, x_58);
return x_18;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_20);
x_59 = lean_box(0);
lean_ctor_set(x_18, 0, x_59);
return x_18;
}
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_68);
lean_dec(x_63);
x_69 = l_Array_isEmpty___redArg(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(x_66, x_64);
lean_dec_ref(x_66);
lean_inc_ref(x_70);
x_71 = l_Lean_mkAppN(x_70, x_67);
lean_dec_ref(x_67);
x_72 = l_Lean_mkAppN(x_70, x_68);
lean_dec_ref(x_68);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_62)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_62;
}
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_60);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_18);
if (x_80 == 0)
{
return x_18;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
lean_dec(x_18);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
return x_14;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_14, 0);
lean_inc(x_84);
lean_dec(x_14);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_86 = !lean_is_exclusive(x_12);
if (x_86 == 0)
{
return x_12;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_12, 0);
lean_inc(x_87);
lean_dec(x_12);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(x_1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proveEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("abstract: (", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") = (", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_74 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
x_75 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(x_74, x_9);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_free_object(x_15);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = lean_box(0);
goto block_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_78 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5;
lean_inc(x_18);
x_79 = l_Lean_MessageData_ofExpr(x_18);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_79);
lean_ctor_set(x_15, 0, x_78);
x_80 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_15);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_19);
x_82 = l_Lean_MessageData_ofExpr(x_19);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(x_74, x_85, x_7, x_8, x_9, x_10);
lean_dec_ref(x_86);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = lean_box(0);
goto block_73;
}
block_73:
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_29 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_18, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_31 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_33 = lean_grind_process_new_facts(x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec_ref(x_33);
x_34 = l_Lean_Meta_Grind_isEqv___redArg(x_30, x_32, x_20);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; 
lean_free_object(x_34);
x_39 = lean_grind_mk_eq_proof(x_30, x_32, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
if (lean_is_scalar(x_16)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_16;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
if (lean_is_scalar(x_16)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_16;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_34, 0);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_grind_mk_eq_proof(x_30, x_32, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_16;
}
lean_ctor_set(x_56, 0, x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_16);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
return x_34;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_34, 0);
lean_inc(x_62);
lean_dec(x_34);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
x_64 = !lean_is_exclusive(x_33);
if (x_64 == 0)
{
return x_33;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_33, 0);
lean_inc(x_65);
lean_dec(x_33);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
return x_31;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_31, 0);
lean_inc(x_68);
lean_dec(x_31);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_29, 0);
lean_inc(x_71);
lean_dec(x_29);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_87 = lean_ctor_get(x_15, 0);
x_88 = lean_ctor_get(x_15, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_15);
x_130 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
x_131 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(x_130, x_9);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
x_89 = x_3;
x_90 = x_4;
x_91 = x_5;
x_92 = x_6;
x_93 = x_7;
x_94 = x_8;
x_95 = x_9;
x_96 = x_10;
x_97 = lean_box(0);
goto block_129;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5;
lean_inc(x_87);
x_135 = l_Lean_MessageData_ofExpr(x_87);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_88);
x_139 = l_Lean_MessageData_ofExpr(x_88);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(x_130, x_142, x_7, x_8, x_9, x_10);
lean_dec_ref(x_143);
x_89 = x_3;
x_90 = x_4;
x_91 = x_5;
x_92 = x_6;
x_93 = x_7;
x_94 = x_8;
x_95 = x_9;
x_96 = x_10;
x_97 = lean_box(0);
goto block_129;
}
block_129:
{
lean_object* x_98; 
lean_inc(x_96);
lean_inc_ref(x_95);
lean_inc(x_94);
lean_inc_ref(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_98 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_87, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
lean_inc(x_96);
lean_inc_ref(x_95);
lean_inc(x_94);
lean_inc_ref(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_100 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
lean_inc(x_96);
lean_inc_ref(x_95);
lean_inc(x_94);
lean_inc_ref(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_102 = lean_grind_process_new_facts(x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
lean_dec_ref(x_102);
x_103 = l_Lean_Meta_Grind_isEqv___redArg(x_99, x_101, x_89);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_unbox(x_104);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_16);
x_107 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
else
{
lean_object* x_109; 
lean_dec(x_105);
x_109 = lean_grind_mk_eq_proof(x_99, x_101, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_16;
}
lean_ctor_set(x_112, 0, x_110);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_16);
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_16);
x_117 = lean_ctor_get(x_103, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_118 = x_103;
} else {
 lean_dec_ref(x_103);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_16);
x_120 = lean_ctor_get(x_102, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_121 = x_102;
} else {
 lean_dec_ref(x_102);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_99);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_16);
x_123 = lean_ctor_get(x_100, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_124 = x_100;
} else {
 lean_dec_ref(x_100);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_16);
x_126 = lean_ctor_get(x_98, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_127 = x_98;
} else {
 lean_dec_ref(x_98);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
}
}
else
{
lean_object* x_144; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_box(0);
lean_ctor_set(x_12, 0, x_144);
return x_12;
}
}
else
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_12, 0);
lean_inc(x_145);
lean_dec(x_12);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_150 = x_146;
} else {
 lean_dec_ref(x_146);
 x_150 = lean_box(0);
}
x_192 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
x_193 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(x_192, x_9);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_dec(x_150);
x_151 = x_3;
x_152 = x_4;
x_153 = x_5;
x_154 = x_6;
x_155 = x_7;
x_156 = x_8;
x_157 = x_9;
x_158 = x_10;
x_159 = lean_box(0);
goto block_191;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_196 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5;
lean_inc(x_148);
x_197 = l_Lean_MessageData_ofExpr(x_148);
if (lean_is_scalar(x_150)) {
 x_198 = lean_alloc_ctor(7, 2, 0);
} else {
 x_198 = x_150;
 lean_ctor_set_tag(x_198, 7);
}
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_inc(x_149);
x_201 = l_Lean_MessageData_ofExpr(x_149);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(x_192, x_204, x_7, x_8, x_9, x_10);
lean_dec_ref(x_205);
x_151 = x_3;
x_152 = x_4;
x_153 = x_5;
x_154 = x_6;
x_155 = x_7;
x_156 = x_8;
x_157 = x_9;
x_158 = x_10;
x_159 = lean_box(0);
goto block_191;
}
block_191:
{
lean_object* x_160; 
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_153);
lean_inc(x_152);
lean_inc(x_151);
x_160 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_148, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_153);
lean_inc(x_152);
lean_inc(x_151);
x_162 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_149, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_153);
lean_inc(x_152);
lean_inc(x_151);
x_164 = lean_grind_process_new_facts(x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec_ref(x_164);
x_165 = l_Lean_Meta_Grind_isEqv___redArg(x_161, x_163, x_151);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = lean_unbox(x_166);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
x_169 = lean_box(0);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 1, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
else
{
lean_object* x_171; 
lean_dec(x_167);
x_171 = lean_grind_mk_eq_proof(x_161, x_163, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_147;
}
lean_ctor_set(x_174, 0, x_172);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 1, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_147);
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_177 = x_171;
} else {
 lean_dec_ref(x_171);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
x_179 = lean_ctor_get(x_165, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_180 = x_165;
} else {
 lean_dec_ref(x_165);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
x_182 = lean_ctor_get(x_164, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_183 = x_164;
} else {
 lean_dec_ref(x_164);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_161);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
x_185 = lean_ctor_get(x_162, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_186 = x_162;
} else {
 lean_dec_ref(x_162);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_147);
x_188 = lean_ctor_get(x_160, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_189 = x_160;
} else {
 lean_dec_ref(x_160);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_188);
return x_190;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_145);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = lean_box(0);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_208 = !lean_is_exclusive(x_12);
if (x_208 == 0)
{
return x_12;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_12, 0);
lean_inc(x_209);
lean_dec(x_12);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_grind_process_new_facts(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l_Lean_Meta_Grind_isEqv___redArg(x_14, x_16, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
if (x_3 == 0)
{
lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; 
lean_free_object(x_18);
x_23 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_free_object(x_18);
x_24 = lean_grind_mk_eq_proof(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
if (x_3 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_grind_mk_eq_proof(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_18, 0);
lean_inc(x_48);
lean_dec(x_18);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_15, 0);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_proveEq_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_proveEq_x3f___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_99; 
x_13 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(x_13, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_box(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed), 12, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
x_99 = lean_unbox(x_15);
lean_dec(x_15);
if (x_99 == 0)
{
x_69 = x_4;
x_70 = x_5;
x_71 = x_6;
x_72 = x_7;
x_73 = x_8;
x_74 = x_9;
x_75 = x_10;
x_76 = x_11;
x_77 = lean_box(0);
goto block_98;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = l_Lean_Meta_Grind_proveEq_x3f___closed__1;
lean_inc_ref(x_1);
x_101 = l_Lean_MessageData_ofExpr(x_1);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_inc_ref(x_2);
x_105 = l_Lean_MessageData_ofExpr(x_2);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg(x_13, x_108, x_8, x_9, x_10, x_11);
lean_dec_ref(x_109);
x_69 = x_4;
x_70 = x_5;
x_71 = x_6;
x_72 = x_7;
x_73 = x_8;
x_74 = x_9;
x_75 = x_10;
x_76 = x_11;
x_77 = lean_box(0);
goto block_98;
}
block_68:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = l_Lean_Meta_Grind_withoutModifyingState___redArg(x_18, x_22, x_26, x_21, x_23, x_19, x_24, x_25, x_20);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec_ref(x_18);
x_31 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_2, x_22);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_16);
if (x_3 == 0)
{
lean_object* x_35; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_31);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 11, 2);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_2);
x_37 = l_Lean_Meta_Grind_withoutModifyingState___redArg(x_36, x_22, x_26, x_21, x_23, x_19, x_24, x_25, x_20);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_free_object(x_31);
x_38 = lean_grind_mk_eq_proof(x_1, x_2, x_22, x_26, x_21, x_23, x_19, x_24, x_25, x_20);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
if (lean_is_scalar(x_16)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_16;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
if (lean_is_scalar(x_16)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_16;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_dec(x_16);
if (x_3 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 11, 2);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_2);
x_53 = l_Lean_Meta_Grind_withoutModifyingState___redArg(x_52, x_22, x_26, x_21, x_23, x_19, x_24, x_25, x_20);
return x_53;
}
}
else
{
lean_object* x_54; 
x_54 = lean_grind_mk_eq_proof(x_1, x_2, x_22, x_26, x_21, x_23, x_19, x_24, x_25, x_20);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_16;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_55);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_16);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
return x_31;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_31, 0);
lean_inc(x_63);
lean_dec(x_31);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_27);
if (x_65 == 0)
{
return x_27;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_27, 0);
lean_inc(x_66);
lean_dec(x_27);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
block_98:
{
lean_object* x_78; 
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_78 = l_Lean_Meta_Grind_hasSameType(x_1, x_2, x_73, x_74, x_75, x_76);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_82 = lean_box(0);
lean_ctor_set(x_78, 0, x_82);
return x_78;
}
else
{
lean_object* x_83; 
lean_free_object(x_78);
x_83 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_69);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
x_19 = x_73;
x_20 = x_76;
x_21 = x_71;
x_22 = x_69;
x_23 = x_72;
x_24 = x_74;
x_25 = x_75;
x_26 = x_70;
x_27 = x_83;
goto block_68;
}
else
{
lean_object* x_86; 
lean_dec_ref(x_83);
x_86 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_2, x_69);
x_19 = x_73;
x_20 = x_76;
x_21 = x_71;
x_22 = x_69;
x_23 = x_72;
x_24 = x_74;
x_25 = x_75;
x_26 = x_70;
x_27 = x_86;
goto block_68;
}
}
else
{
x_19 = x_73;
x_20 = x_76;
x_21 = x_71;
x_22 = x_69;
x_23 = x_72;
x_24 = x_74;
x_25 = x_75;
x_26 = x_70;
x_27 = x_83;
goto block_68;
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
lean_dec(x_78);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
else
{
lean_object* x_91; 
x_91 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_69);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
x_19 = x_73;
x_20 = x_76;
x_21 = x_71;
x_22 = x_69;
x_23 = x_72;
x_24 = x_74;
x_25 = x_75;
x_26 = x_70;
x_27 = x_91;
goto block_68;
}
else
{
lean_object* x_94; 
lean_dec_ref(x_91);
x_94 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_2, x_69);
x_19 = x_73;
x_20 = x_76;
x_21 = x_71;
x_22 = x_69;
x_23 = x_72;
x_24 = x_74;
x_25 = x_75;
x_26 = x_70;
x_27 = x_94;
goto block_68;
}
}
else
{
x_19 = x_73;
x_20 = x_76;
x_21 = x_71;
x_22 = x_69;
x_23 = x_72;
x_24 = x_74;
x_25 = x_75;
x_26 = x_70;
x_27 = x_91;
goto block_68;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_78);
if (x_95 == 0)
{
return x_78;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_78, 0);
lean_inc(x_96);
lean_dec(x_78);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Meta_Grind_proveEq_x3f___lam__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Meta_Grind_proveEq_x3f(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_grind_process_new_facts(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = l_Lean_Meta_Grind_isEqv___redArg(x_13, x_15, x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = lean_grind_mk_heq_proof(x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_grind_mk_heq_proof(x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
return x_16;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_14, 0);
lean_inc(x_51);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
return x_12;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_51; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed), 11, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_51 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_3);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
x_13 = x_51;
goto block_50;
}
else
{
lean_object* x_54; 
lean_dec_ref(x_51);
x_54 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_2, x_3);
x_13 = x_54;
goto block_50;
}
}
else
{
x_13 = x_51;
goto block_50;
}
block_50:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = l_Lean_Meta_Grind_withoutModifyingState___redArg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_12);
x_17 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = lean_grind_mk_heq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_grind_mk_heq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_proveHEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__1___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9);
l_Lean_Meta_Grind_proveEq_x3f___closed__0 = _init_l_Lean_Meta_Grind_proveEq_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_proveEq_x3f___closed__0);
l_Lean_Meta_Grind_proveEq_x3f___closed__1 = _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_proveEq_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
