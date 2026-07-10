// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProveEq
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Lean.Meta.Tactic.Grind.Simp
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_withoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "abstractFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 46, 159, 125, 153, 141, 125, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proveEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value),LEAN_SCALAR_PTR_LITERAL(80, 31, 36, 78, 142, 219, 66, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "abstract: ("};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ") = ("};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_proveEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Grind_proveEq_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_proveEq_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_proveEq_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_proveEq_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_31_, v___y_39_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(lean_object* v_e_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(v_e_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(lean_object* v_e_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_57_, v_a_58_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_101_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_101_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_101_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_101_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v___x_74_; 
v___x_74_ = lean_unbox(v_a_70_);
lean_dec(v_a_70_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v_a_76_; lean_object* v___x_77_; 
lean_del_object(v___x_72_);
v___x_75_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_57_, v_a_65_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_76_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_n(v_a_78_, 2);
lean_dec_ref_known(v___x_77_, 1);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_box(0);
lean_inc(v_a_67_);
lean_inc_ref(v_a_66_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc(v_a_61_);
lean_inc_ref(v_a_60_);
lean_inc(v_a_59_);
lean_inc(v_a_58_);
v___x_81_ = lean_grind_internalize(v_a_78_, v___x_79_, v___x_80_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_89_);
v___x_83_ = v___x_81_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_81_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_a_78_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_78_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
lean_dec(v_a_78_);
v_a_90_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_81_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_81_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
return v___x_77_;
}
}
else
{
lean_object* v___x_99_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_e_57_);
v___x_99_ = v___x_72_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_e_57_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_e_57_);
v_a_102_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_69_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_69_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(lean_object* v_e_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_e_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec(v_a_111_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_nat_dec_lt(v___x_126_, v_a_123_);
v___x_128_ = lean_box(v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_a_124_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_132_, v_a_133_);
lean_dec(v_a_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_136_, v_a_137_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec(v_a_152_);
lean_dec(v_a_150_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_a_165_, v___x_178_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc(v_a_168_);
lean_inc(v_a_167_);
v___x_180_ = lean_apply_13(v_x_164_, v___x_179_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, lean_box(0));
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(lean_object* v_x_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(v_x_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec(v_a_184_);
lean_dec(v_a_182_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_object* v_00_u03b1_196_, lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_a_198_, v___x_211_);
lean_inc(v_a_209_);
lean_inc_ref(v_a_208_);
lean_inc(v_a_207_);
lean_inc_ref(v_a_206_);
lean_inc(v_a_205_);
lean_inc_ref(v_a_204_);
lean_inc(v_a_203_);
lean_inc_ref(v_a_202_);
lean_inc(v_a_201_);
lean_inc(v_a_200_);
v___x_213_ = lean_apply_13(v_x_197_, v___x_212_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, lean_box(0));
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(v_00_u03b1_214_, v_x_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec(v_a_218_);
lean_dec(v_a_216_);
return v_res_229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2(void){
_start:
{
lean_object* v_i_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_i_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1));
v___x_235_ = lean_name_append_index_after(v___x_234_, v_i_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(lean_object* v_as_236_, size_t v_sz_237_, size_t v_i_238_, lean_object* v_b_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_lt(v_i_238_, v_sz_237_);
if (v___x_240_ == 0)
{
return v_b_239_;
}
else
{
lean_object* v_a_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; size_t v___x_245_; size_t v___x_246_; 
v_a_241_ = lean_array_uget_borrowed(v_as_236_, v_i_238_);
v___x_242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2);
v___x_243_ = 0;
lean_inc(v_a_241_);
v___x_244_ = l_Lean_mkLambda(v___x_242_, v___x_243_, v_a_241_, v_b_239_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_add(v_i_238_, v___x_245_);
v_i_238_ = v___x_246_;
v_b_239_ = v___x_244_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(lean_object* v_as_248_, lean_object* v_sz_249_, lean_object* v_i_250_, lean_object* v_b_251_){
_start:
{
size_t v_sz_boxed_252_; size_t v_i_boxed_253_; lean_object* v_res_254_; 
v_sz_boxed_252_ = lean_unbox_usize(v_sz_249_);
lean_dec(v_sz_249_);
v_i_boxed_253_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_as_248_, v_sz_boxed_252_, v_i_boxed_253_, v_b_251_);
lean_dec_ref(v_as_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(lean_object* v_varTypes_255_, lean_object* v_b_256_){
_start:
{
size_t v_sz_257_; size_t v___x_258_; lean_object* v___x_259_; 
v_sz_257_ = lean_array_size(v_varTypes_255_);
v___x_258_ = ((size_t)0ULL);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_varTypes_255_, v_sz_257_, v___x_258_, v_b_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(lean_object* v_varTypes_260_, lean_object* v_b_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_260_, v_b_261_);
lean_dec_ref(v_varTypes_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(lean_object* v_a_263_, lean_object* v_x_264_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_key_266_; lean_object* v_value_267_; lean_object* v_tail_268_; uint8_t v___y_270_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; uint8_t v___x_277_; 
v_key_266_ = lean_ctor_get(v_x_264_, 0);
v_value_267_ = lean_ctor_get(v_x_264_, 1);
v_tail_268_ = lean_ctor_get(v_x_264_, 2);
v_fst_273_ = lean_ctor_get(v_key_266_, 0);
v_snd_274_ = lean_ctor_get(v_key_266_, 1);
v_fst_275_ = lean_ctor_get(v_a_263_, 0);
v_snd_276_ = lean_ctor_get(v_a_263_, 1);
v___x_277_ = lean_expr_eqv(v_fst_273_, v_fst_275_);
if (v___x_277_ == 0)
{
v___y_270_ = v___x_277_;
goto v___jp_269_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = lean_expr_eqv(v_snd_274_, v_snd_276_);
v___y_270_ = v___x_278_;
goto v___jp_269_;
}
v___jp_269_:
{
if (v___y_270_ == 0)
{
v_x_264_ = v_tail_268_;
goto _start;
}
else
{
lean_object* v___x_272_; 
lean_inc(v_value_267_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_value_267_);
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_279_, v_x_280_);
lean_dec(v_x_280_);
lean_dec_ref(v_a_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_buckets_284_; lean_object* v_fst_285_; lean_object* v_snd_286_; lean_object* v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_buckets_284_ = lean_ctor_get(v_m_282_, 1);
v_fst_285_ = lean_ctor_get(v_a_283_, 0);
v_snd_286_ = lean_ctor_get(v_a_283_, 1);
v___x_287_ = lean_array_get_size(v_buckets_284_);
v___x_288_ = l_Lean_Expr_hash(v_fst_285_);
v___x_289_ = l_Lean_Expr_hash(v_snd_286_);
v___x_290_ = lean_uint64_mix_hash(v___x_288_, v___x_289_);
v___x_291_ = 32ULL;
v___x_292_ = lean_uint64_shift_right(v___x_290_, v___x_291_);
v_fold_293_ = lean_uint64_xor(v___x_290_, v___x_292_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_287_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v___x_302_ = lean_array_uget_borrowed(v_buckets_284_, v___x_301_);
v___x_303_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_283_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(lean_object* v_m_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_304_, v_a_305_);
lean_dec_ref(v_a_305_);
lean_dec_ref(v_m_304_);
return v_res_306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 0;
return v___x_309_;
}
else
{
lean_object* v_key_310_; lean_object* v_tail_311_; uint8_t v___y_313_; lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v_fst_317_; lean_object* v_snd_318_; uint8_t v___x_319_; 
v_key_310_ = lean_ctor_get(v_x_308_, 0);
v_tail_311_ = lean_ctor_get(v_x_308_, 2);
v_fst_315_ = lean_ctor_get(v_key_310_, 0);
v_snd_316_ = lean_ctor_get(v_key_310_, 1);
v_fst_317_ = lean_ctor_get(v_a_307_, 0);
v_snd_318_ = lean_ctor_get(v_a_307_, 1);
v___x_319_ = lean_expr_eqv(v_fst_315_, v_fst_317_);
if (v___x_319_ == 0)
{
v___y_313_ = v___x_319_;
goto v___jp_312_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = lean_expr_eqv(v_snd_316_, v_snd_318_);
v___y_313_ = v___x_320_;
goto v___jp_312_;
}
v___jp_312_:
{
if (v___y_313_ == 0)
{
v_x_308_ = v_tail_311_;
goto _start;
}
else
{
return v___y_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec_ref(v_a_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(lean_object* v_a_325_, lean_object* v_b_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_dec(v_b_326_);
lean_dec_ref(v_a_325_);
return v_x_327_;
}
else
{
lean_object* v_key_328_; lean_object* v_value_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_349_; 
v_key_328_ = lean_ctor_get(v_x_327_, 0);
v_value_329_ = lean_ctor_get(v_x_327_, 1);
v_tail_330_ = lean_ctor_get(v_x_327_, 2);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_349_ == 0)
{
v___x_332_ = v_x_327_;
v_isShared_333_ = v_isSharedCheck_349_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_value_329_);
lean_inc(v_key_328_);
lean_dec(v_x_327_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_349_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
uint8_t v___y_335_; lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; uint8_t v___x_347_; 
v_fst_343_ = lean_ctor_get(v_key_328_, 0);
v_snd_344_ = lean_ctor_get(v_key_328_, 1);
v_fst_345_ = lean_ctor_get(v_a_325_, 0);
v_snd_346_ = lean_ctor_get(v_a_325_, 1);
v___x_347_ = lean_expr_eqv(v_fst_343_, v_fst_345_);
if (v___x_347_ == 0)
{
v___y_335_ = v___x_347_;
goto v___jp_334_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = lean_expr_eqv(v_snd_344_, v_snd_346_);
v___y_335_ = v___x_348_;
goto v___jp_334_;
}
v___jp_334_:
{
if (v___y_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_325_, v_b_326_, v_tail_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 2, v___x_336_);
v___x_338_ = v___x_332_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_key_328_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_value_329_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v___x_341_; 
lean_dec(v_value_329_);
lean_dec(v_key_328_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_b_326_);
lean_ctor_set(v___x_332_, 0, v_a_325_);
v___x_341_ = v___x_332_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_325_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_b_326_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_tail_330_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
return v_x_350_;
}
else
{
lean_object* v_key_352_; lean_object* v_value_353_; lean_object* v_tail_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_381_; 
v_key_352_ = lean_ctor_get(v_x_351_, 0);
v_value_353_ = lean_ctor_get(v_x_351_, 1);
v_tail_354_ = lean_ctor_get(v_x_351_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_381_ == 0)
{
v___x_356_ = v_x_351_;
v_isShared_357_ = v_isSharedCheck_381_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_tail_354_);
lean_inc(v_value_353_);
lean_inc(v_key_352_);
lean_dec(v_x_351_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_381_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v_fold_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v_fst_358_ = lean_ctor_get(v_key_352_, 0);
v_snd_359_ = lean_ctor_get(v_key_352_, 1);
v___x_360_ = lean_array_get_size(v_x_350_);
v___x_361_ = l_Lean_Expr_hash(v_fst_358_);
v___x_362_ = l_Lean_Expr_hash(v_snd_359_);
v___x_363_ = lean_uint64_mix_hash(v___x_361_, v___x_362_);
v___x_364_ = 32ULL;
v___x_365_ = lean_uint64_shift_right(v___x_363_, v___x_364_);
v_fold_366_ = lean_uint64_xor(v___x_363_, v___x_365_);
v___x_367_ = 16ULL;
v___x_368_ = lean_uint64_shift_right(v_fold_366_, v___x_367_);
v___x_369_ = lean_uint64_xor(v_fold_366_, v___x_368_);
v___x_370_ = lean_uint64_to_usize(v___x_369_);
v___x_371_ = lean_usize_of_nat(v___x_360_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_sub(v___x_371_, v___x_372_);
v___x_374_ = lean_usize_land(v___x_370_, v___x_373_);
v___x_375_ = lean_array_uget_borrowed(v_x_350_, v___x_374_);
lean_inc(v___x_375_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 2, v___x_375_);
v___x_377_ = v___x_356_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_key_352_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_value_353_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v___x_375_);
v___x_377_ = v_reuseFailAlloc_380_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_array_uset(v_x_350_, v___x_374_, v___x_377_);
v_x_350_ = v___x_378_;
v_x_351_ = v_tail_354_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(lean_object* v_i_382_, lean_object* v_source_383_, lean_object* v_target_384_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_array_get_size(v_source_383_);
v___x_386_ = lean_nat_dec_lt(v_i_382_, v___x_385_);
if (v___x_386_ == 0)
{
lean_dec_ref(v_source_383_);
lean_dec(v_i_382_);
return v_target_384_;
}
else
{
lean_object* v_es_387_; lean_object* v___x_388_; lean_object* v_source_389_; lean_object* v_target_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_es_387_ = lean_array_fget(v_source_383_, v_i_382_);
v___x_388_ = lean_box(0);
v_source_389_ = lean_array_fset(v_source_383_, v_i_382_, v___x_388_);
v_target_390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_target_384_, v_es_387_);
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_add(v_i_382_, v___x_391_);
lean_dec(v_i_382_);
v_i_382_ = v___x_392_;
v_source_383_ = v_source_389_;
v_target_384_ = v_target_390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(lean_object* v_data_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_nbuckets_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_395_ = lean_array_get_size(v_data_394_);
v___x_396_ = lean_unsigned_to_nat(2u);
v_nbuckets_397_ = lean_nat_mul(v___x_395_, v___x_396_);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_box(0);
v___x_400_ = lean_mk_array(v_nbuckets_397_, v___x_399_);
v___x_401_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v___x_398_, v_data_394_, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object* v_m_402_, lean_object* v_a_403_, lean_object* v_b_404_){
_start:
{
lean_object* v_size_405_; lean_object* v_buckets_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_453_; 
v_size_405_ = lean_ctor_get(v_m_402_, 0);
v_buckets_406_ = lean_ctor_get(v_m_402_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_m_402_);
if (v_isSharedCheck_453_ == 0)
{
v___x_408_ = v_m_402_;
v_isShared_409_ = v_isSharedCheck_453_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_buckets_406_);
lean_inc(v_size_405_);
lean_dec(v_m_402_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_453_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v_fold_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v_bkt_427_; uint8_t v___x_428_; 
v_fst_410_ = lean_ctor_get(v_a_403_, 0);
v_snd_411_ = lean_ctor_get(v_a_403_, 1);
v___x_412_ = lean_array_get_size(v_buckets_406_);
v___x_413_ = l_Lean_Expr_hash(v_fst_410_);
v___x_414_ = l_Lean_Expr_hash(v_snd_411_);
v___x_415_ = lean_uint64_mix_hash(v___x_413_, v___x_414_);
v___x_416_ = 32ULL;
v___x_417_ = lean_uint64_shift_right(v___x_415_, v___x_416_);
v_fold_418_ = lean_uint64_xor(v___x_415_, v___x_417_);
v___x_419_ = 16ULL;
v___x_420_ = lean_uint64_shift_right(v_fold_418_, v___x_419_);
v___x_421_ = lean_uint64_xor(v_fold_418_, v___x_420_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = lean_usize_of_nat(v___x_412_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_sub(v___x_423_, v___x_424_);
v___x_426_ = lean_usize_land(v___x_422_, v___x_425_);
v_bkt_427_ = lean_array_uget_borrowed(v_buckets_406_, v___x_426_);
v___x_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_403_, v_bkt_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_size_x27_430_; lean_object* v___x_431_; lean_object* v_buckets_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v_size_x27_430_ = lean_nat_add(v_size_405_, v___x_429_);
lean_dec(v_size_405_);
lean_inc(v_bkt_427_);
v___x_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_431_, 0, v_a_403_);
lean_ctor_set(v___x_431_, 1, v_b_404_);
lean_ctor_set(v___x_431_, 2, v_bkt_427_);
v_buckets_x27_432_ = lean_array_uset(v_buckets_406_, v___x_426_, v___x_431_);
v___x_433_ = lean_unsigned_to_nat(4u);
v___x_434_ = lean_nat_mul(v_size_x27_430_, v___x_433_);
v___x_435_ = lean_unsigned_to_nat(3u);
v___x_436_ = lean_nat_div(v___x_434_, v___x_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_array_get_size(v_buckets_x27_432_);
v___x_438_ = lean_nat_dec_le(v___x_436_, v___x_437_);
lean_dec(v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v_val_439_; lean_object* v___x_441_; 
v_val_439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_buckets_x27_432_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v_val_439_);
lean_ctor_set(v___x_408_, 0, v_size_x27_430_);
v___x_441_ = v___x_408_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_size_x27_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_val_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_444_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v_buckets_x27_432_);
lean_ctor_set(v___x_408_, 0, v_size_x27_430_);
v___x_444_ = v___x_408_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_size_x27_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_buckets_x27_432_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_446_; lean_object* v_buckets_x27_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_bkt_427_);
v___x_446_ = lean_box(0);
v_buckets_x27_447_ = lean_array_uset(v_buckets_406_, v___x_426_, v___x_446_);
v___x_448_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_403_, v_b_404_, v_bkt_427_);
v___x_449_ = lean_array_uset(v_buckets_x27_447_, v___x_426_, v___x_448_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_449_);
v___x_451_ = v___x_408_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_size_405_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object* v_lhs_454_, lean_object* v_rhs_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___x_517_; 
v___x_517_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_881_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_881_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_881_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_881_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
if (lean_obj_tag(v_a_518_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v___x_522_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_880_; 
v_val_526_ = lean_ctor_get(v_a_518_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_880_ == 0)
{
v___x_528_ = v_a_518_;
v_isShared_529_ = v_isSharedCheck_880_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_a_518_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_880_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_879_; 
v_fst_530_ = lean_ctor_get(v_val_526_, 0);
v_snd_531_ = lean_ctor_get(v_val_526_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_val_526_);
if (v_isSharedCheck_879_ == 0)
{
v___x_533_ = v_val_526_;
v_isShared_534_ = v_isSharedCheck_879_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
lean_dec(v_val_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_879_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; uint8_t v___y_782_; uint8_t v___x_874_; 
v___x_874_ = lean_unbox(v_fst_530_);
lean_dec(v_fst_530_);
if (v___x_874_ == 0)
{
lean_del_object(v___x_533_);
lean_del_object(v___x_528_);
v___y_536_ = v_a_456_;
v___y_537_ = v_a_458_;
v___y_538_ = v_a_459_;
v___y_539_ = v_a_460_;
v___y_540_ = v_a_461_;
v___y_541_ = v_a_462_;
v___y_542_ = v_a_463_;
v___y_543_ = v_a_464_;
v___y_544_ = v_a_465_;
v___y_545_ = v_a_466_;
v___y_546_ = v_a_467_;
goto v___jp_535_;
}
else
{
uint8_t v___x_875_; uint8_t v___x_876_; 
v___x_875_ = l_Lean_Expr_hasLooseBVars(v_lhs_454_);
v___x_876_ = lean_bool_not(v___x_875_);
if (v___x_876_ == 0)
{
v___y_782_ = v___x_876_;
goto v___jp_781_;
}
else
{
uint8_t v___x_877_; uint8_t v___x_878_; 
v___x_877_ = l_Lean_Expr_hasLooseBVars(v_rhs_455_);
v___x_878_ = lean_bool_not(v___x_877_);
v___y_782_ = v___x_878_;
goto v___jp_781_;
}
}
v___jp_535_:
{
switch(lean_obj_tag(v_lhs_454_))
{
case 5:
{
if (lean_obj_tag(v_rhs_455_) == 5)
{
lean_object* v_fn_547_; lean_object* v_arg_548_; lean_object* v_fn_549_; lean_object* v_arg_550_; lean_object* v___x_551_; 
lean_del_object(v___x_520_);
v_fn_547_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc_ref(v_fn_547_);
v_arg_548_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_arg_548_);
lean_dec_ref_known(v_lhs_454_, 2);
v_fn_549_ = lean_ctor_get(v_rhs_455_, 0);
lean_inc_ref(v_fn_549_);
v_arg_550_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_arg_550_);
lean_dec_ref_known(v_rhs_455_, 2);
v___x_551_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_fn_547_, v_fn_549_, v___y_536_, v_snd_531_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
if (lean_obj_tag(v_a_552_) == 0)
{
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_548_);
return v___x_551_;
}
else
{
lean_object* v_val_553_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_556_; 
lean_dec_ref_known(v___x_551_, 1);
v_val_553_ = lean_ctor_get(v_a_552_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_a_552_, 1);
v_fst_554_ = lean_ctor_get(v_val_553_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v_val_553_, 1);
lean_inc(v_snd_555_);
lean_dec(v_val_553_);
v___x_556_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_arg_548_, v_arg_550_, v___y_536_, v_snd_555_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
if (lean_obj_tag(v_a_557_) == 0)
{
lean_dec(v_fst_554_);
return v___x_556_;
}
else
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_582_; 
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_556_, 0);
lean_dec(v_unused_583_);
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_582_;
goto v_resetjp_558_;
}
else
{
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_582_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_val_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_581_; 
v_val_561_ = lean_ctor_get(v_a_557_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_581_ == 0)
{
v___x_563_ = v_a_557_;
v_isShared_564_ = v_isSharedCheck_581_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_val_561_);
lean_dec(v_a_557_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_581_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_580_; 
v_fst_565_ = lean_ctor_get(v_val_561_, 0);
v_snd_566_ = lean_ctor_get(v_val_561_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_val_561_);
if (v_isSharedCheck_580_ == 0)
{
v___x_568_ = v_val_561_;
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v_val_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = l_Lean_Expr_app___override(v_fst_554_, v_fst_565_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_566_);
v___x_572_ = v_reuseFailAlloc_579_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_572_);
v___x_574_ = v___x_563_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_574_);
v___x_576_ = v___x_559_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
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
lean_dec(v_fst_554_);
return v___x_556_;
}
}
}
else
{
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_548_);
return v___x_551_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_586_; 
lean_dec_ref_known(v_lhs_454_, 2);
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
v___x_584_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_584_);
v___x_586_ = v___x_520_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
case 6:
{
if (lean_obj_tag(v_rhs_455_) == 6)
{
lean_object* v_binderName_588_; lean_object* v_binderType_589_; lean_object* v_body_590_; uint8_t v_binderInfo_591_; lean_object* v_binderType_592_; lean_object* v_body_593_; lean_object* v___x_594_; 
lean_del_object(v___x_520_);
v_binderName_588_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_binderName_588_);
v_binderType_589_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_binderType_589_);
v_body_590_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_body_590_);
v_binderInfo_591_ = lean_ctor_get_uint8(v_lhs_454_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_454_, 3);
v_binderType_592_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_binderType_592_);
v_body_593_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_body_593_);
lean_dec_ref_known(v_rhs_455_, 3);
v___x_594_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_589_, v_binderType_592_, v___y_536_, v_snd_531_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
if (lean_obj_tag(v_a_595_) == 0)
{
lean_dec_ref(v_body_593_);
lean_dec_ref(v_body_590_);
lean_dec(v_binderName_588_);
return v___x_594_;
}
else
{
lean_object* v_val_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref_known(v___x_594_, 1);
v_val_596_ = lean_ctor_get(v_a_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_a_595_, 1);
v_fst_597_ = lean_ctor_get(v_val_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v_val_596_, 1);
lean_inc(v_snd_598_);
lean_dec(v_val_596_);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v___y_536_, v___x_599_);
v___x_601_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_590_, v_body_593_, v___x_600_, v_snd_598_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___x_600_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
if (lean_obj_tag(v_a_602_) == 0)
{
lean_dec(v_fst_597_);
lean_dec(v_binderName_588_);
return v___x_601_;
}
else
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_628_);
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_627_;
goto v_resetjp_603_;
}
else
{
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_627_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_626_; 
v_val_606_ = lean_ctor_get(v_a_602_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_626_ == 0)
{
v___x_608_ = v_a_602_;
v_isShared_609_ = v_isSharedCheck_626_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v_a_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_626_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_625_; 
v_fst_610_ = lean_ctor_get(v_val_606_, 0);
v_snd_611_ = lean_ctor_get(v_val_606_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_val_606_);
if (v_isSharedCheck_625_ == 0)
{
v___x_613_ = v_val_606_;
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v_val_606_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_mkLambda(v_binderName_588_, v_binderInfo_591_, v_fst_597_, v_fst_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_snd_611_);
v___x_617_ = v_reuseFailAlloc_624_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_617_);
v___x_619_ = v___x_608_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_619_);
v___x_621_ = v___x_604_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
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
lean_dec(v_fst_597_);
lean_dec(v_binderName_588_);
return v___x_601_;
}
}
}
else
{
lean_dec_ref(v_body_593_);
lean_dec_ref(v_body_590_);
lean_dec(v_binderName_588_);
return v___x_594_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_dec_ref_known(v_lhs_454_, 3);
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
v___x_629_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_629_);
v___x_631_ = v___x_520_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
case 7:
{
if (lean_obj_tag(v_rhs_455_) == 7)
{
lean_object* v_binderName_633_; lean_object* v_binderType_634_; lean_object* v_body_635_; uint8_t v_binderInfo_636_; lean_object* v_binderType_637_; lean_object* v_body_638_; lean_object* v___x_639_; 
lean_del_object(v___x_520_);
v_binderName_633_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_binderName_633_);
v_binderType_634_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_binderType_634_);
v_body_635_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_body_635_);
v_binderInfo_636_ = lean_ctor_get_uint8(v_lhs_454_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_454_, 3);
v_binderType_637_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_binderType_637_);
v_body_638_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_body_638_);
lean_dec_ref_known(v_rhs_455_, 3);
v___x_639_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_634_, v_binderType_637_, v___y_536_, v_snd_531_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
if (lean_obj_tag(v_a_640_) == 0)
{
lean_dec_ref(v_body_638_);
lean_dec_ref(v_body_635_);
lean_dec(v_binderName_633_);
return v___x_639_;
}
else
{
lean_object* v_val_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec_ref_known(v___x_639_, 1);
v_val_641_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_a_640_, 1);
v_fst_642_ = lean_ctor_get(v_val_641_, 0);
lean_inc(v_fst_642_);
v_snd_643_ = lean_ctor_get(v_val_641_, 1);
lean_inc(v_snd_643_);
lean_dec(v_val_641_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v___y_536_, v___x_644_);
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_635_, v_body_638_, v___x_645_, v_snd_643_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___x_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
if (lean_obj_tag(v_a_647_) == 0)
{
lean_dec(v_fst_642_);
lean_dec(v_binderName_633_);
return v___x_646_;
}
else
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_672_; 
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_646_, 0);
lean_dec(v_unused_673_);
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_672_;
goto v_resetjp_648_;
}
else
{
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_672_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_671_; 
v_val_651_ = lean_ctor_get(v_a_647_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_671_ == 0)
{
v___x_653_ = v_a_647_;
v_isShared_654_ = v_isSharedCheck_671_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v_a_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_671_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_670_; 
v_fst_655_ = lean_ctor_get(v_val_651_, 0);
v_snd_656_ = lean_ctor_get(v_val_651_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_val_651_);
if (v_isSharedCheck_670_ == 0)
{
v___x_658_ = v_val_651_;
v_isShared_659_ = v_isSharedCheck_670_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec(v_val_651_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_670_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_mkForall(v_binderName_633_, v_binderInfo_636_, v_fst_642_, v_fst_655_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_656_);
v___x_662_ = v_reuseFailAlloc_669_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_662_);
v___x_664_ = v___x_653_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_664_);
v___x_666_ = v___x_649_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
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
lean_dec(v_fst_642_);
lean_dec(v_binderName_633_);
return v___x_646_;
}
}
}
else
{
lean_dec_ref(v_body_638_);
lean_dec_ref(v_body_635_);
lean_dec(v_binderName_633_);
return v___x_639_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_dec_ref_known(v_lhs_454_, 3);
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
v___x_674_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_674_);
v___x_676_ = v___x_520_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
case 8:
{
if (lean_obj_tag(v_rhs_455_) == 8)
{
lean_object* v_declName_678_; lean_object* v_type_679_; lean_object* v_value_680_; lean_object* v_body_681_; uint8_t v_nondep_682_; lean_object* v_type_683_; lean_object* v_value_684_; lean_object* v_body_685_; lean_object* v___x_686_; 
lean_del_object(v___x_520_);
v_declName_678_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_declName_678_);
v_type_679_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_type_679_);
v_value_680_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_value_680_);
v_body_681_ = lean_ctor_get(v_lhs_454_, 3);
lean_inc_ref(v_body_681_);
v_nondep_682_ = lean_ctor_get_uint8(v_lhs_454_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_lhs_454_, 4);
v_type_683_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_type_683_);
v_value_684_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_value_684_);
v_body_685_ = lean_ctor_get(v_rhs_455_, 3);
lean_inc_ref(v_body_685_);
lean_dec_ref_known(v_rhs_455_, 4);
v___x_686_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_type_679_, v_type_683_, v___y_536_, v_snd_531_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
if (lean_obj_tag(v_a_687_) == 0)
{
lean_dec_ref(v_body_685_);
lean_dec_ref(v_value_684_);
lean_dec_ref(v_body_681_);
lean_dec_ref(v_value_680_);
lean_dec(v_declName_678_);
return v___x_686_;
}
else
{
lean_object* v_val_688_; lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_691_; 
lean_dec_ref_known(v___x_686_, 1);
v_val_688_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_a_687_, 1);
v_fst_689_ = lean_ctor_get(v_val_688_, 0);
lean_inc(v_fst_689_);
v_snd_690_ = lean_ctor_get(v_val_688_, 1);
lean_inc(v_snd_690_);
lean_dec(v_val_688_);
v___x_691_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_value_680_, v_value_684_, v___y_536_, v_snd_690_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
if (lean_obj_tag(v_a_692_) == 0)
{
lean_dec(v_fst_689_);
lean_dec_ref(v_body_685_);
lean_dec_ref(v_body_681_);
lean_dec(v_declName_678_);
return v___x_691_;
}
else
{
lean_object* v_val_693_; lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec_ref_known(v___x_691_, 1);
v_val_693_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v_a_692_, 1);
v_fst_694_ = lean_ctor_get(v_val_693_, 0);
lean_inc(v_fst_694_);
v_snd_695_ = lean_ctor_get(v_val_693_, 1);
lean_inc(v_snd_695_);
lean_dec(v_val_693_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v___y_536_, v___x_696_);
v___x_698_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_681_, v_body_685_, v___x_697_, v_snd_695_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___x_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
if (lean_obj_tag(v_a_699_) == 0)
{
lean_dec(v_fst_694_);
lean_dec(v_fst_689_);
lean_dec(v_declName_678_);
return v___x_698_;
}
else
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_698_, 0);
lean_dec(v_unused_725_);
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_724_;
goto v_resetjp_700_;
}
else
{
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_724_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_723_; 
v_val_703_ = lean_ctor_get(v_a_699_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_699_);
if (v_isSharedCheck_723_ == 0)
{
v___x_705_ = v_a_699_;
v_isShared_706_ = v_isSharedCheck_723_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v_a_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_723_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_fst_707_; lean_object* v_snd_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_722_; 
v_fst_707_ = lean_ctor_get(v_val_703_, 0);
v_snd_708_ = lean_ctor_get(v_val_703_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_val_703_);
if (v_isSharedCheck_722_ == 0)
{
v___x_710_ = v_val_703_;
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_snd_708_);
lean_inc(v_fst_707_);
lean_dec(v_val_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = l_Lean_Expr_letE___override(v_declName_678_, v_fst_689_, v_fst_694_, v_fst_707_, v_nondep_682_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_708_);
v___x_714_ = v_reuseFailAlloc_721_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_714_);
v___x_716_ = v___x_705_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_716_);
v___x_718_ = v___x_701_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
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
lean_dec(v_fst_694_);
lean_dec(v_fst_689_);
lean_dec(v_declName_678_);
return v___x_698_;
}
}
}
else
{
lean_dec(v_fst_689_);
lean_dec_ref(v_body_685_);
lean_dec_ref(v_body_681_);
lean_dec(v_declName_678_);
return v___x_691_;
}
}
}
else
{
lean_dec_ref(v_body_685_);
lean_dec_ref(v_value_684_);
lean_dec_ref(v_body_681_);
lean_dec_ref(v_value_680_);
lean_dec(v_declName_678_);
return v___x_686_;
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec_ref_known(v_lhs_454_, 4);
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
v___x_726_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_726_);
v___x_728_ = v___x_520_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
case 10:
{
if (lean_obj_tag(v_rhs_455_) == 10)
{
lean_object* v_data_730_; lean_object* v_expr_731_; lean_object* v_expr_732_; lean_object* v___x_733_; 
lean_del_object(v___x_520_);
v_data_730_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_data_730_);
v_expr_731_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_expr_731_);
lean_dec_ref_known(v_lhs_454_, 2);
v_expr_732_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_expr_732_);
lean_dec_ref_known(v_rhs_455_, 2);
v___x_733_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_expr_731_, v_expr_732_, v___y_536_, v_snd_531_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
if (lean_obj_tag(v_a_734_) == 0)
{
lean_dec(v_data_730_);
return v___x_733_;
}
else
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_759_; 
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_733_, 0);
lean_dec(v_unused_760_);
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
else
{
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_val_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_758_; 
v_val_738_ = lean_ctor_get(v_a_734_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_758_ == 0)
{
v___x_740_ = v_a_734_;
v_isShared_741_ = v_isSharedCheck_758_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_val_738_);
lean_dec(v_a_734_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_758_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_fst_742_; lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_757_; 
v_fst_742_ = lean_ctor_get(v_val_738_, 0);
v_snd_743_ = lean_ctor_get(v_val_738_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_val_738_);
if (v_isSharedCheck_757_ == 0)
{
v___x_745_ = v_val_738_;
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_inc(v_fst_742_);
lean_dec(v_val_738_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = l_Lean_Expr_mdata___override(v_data_730_, v_fst_742_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_snd_743_);
v___x_749_ = v_reuseFailAlloc_756_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_749_);
v___x_751_ = v___x_740_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_751_);
v___x_753_ = v___x_736_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
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
lean_dec(v_data_730_);
return v___x_733_;
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec_ref_known(v_lhs_454_, 2);
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
v___x_761_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_761_);
v___x_763_ = v___x_520_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
case 11:
{
if (lean_obj_tag(v_rhs_455_) == 11)
{
lean_object* v_typeName_765_; lean_object* v_idx_766_; lean_object* v_struct_767_; lean_object* v_typeName_768_; lean_object* v_idx_769_; lean_object* v_struct_770_; uint8_t v___x_771_; 
lean_del_object(v___x_520_);
v_typeName_765_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_typeName_765_);
v_idx_766_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc(v_idx_766_);
v_struct_767_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_struct_767_);
lean_dec_ref_known(v_lhs_454_, 3);
v_typeName_768_ = lean_ctor_get(v_rhs_455_, 0);
lean_inc(v_typeName_768_);
v_idx_769_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc(v_idx_769_);
v_struct_770_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_struct_770_);
lean_dec_ref_known(v_rhs_455_, 3);
v___x_771_ = lean_name_eq(v_typeName_765_, v_typeName_768_);
lean_dec(v_typeName_768_);
if (v___x_771_ == 0)
{
lean_dec(v_idx_769_);
v___y_470_ = v___y_539_;
v___y_471_ = v___y_546_;
v___y_472_ = v___y_543_;
v___y_473_ = v_idx_766_;
v___y_474_ = v___y_538_;
v___y_475_ = v___y_542_;
v___y_476_ = v___y_545_;
v___y_477_ = v___y_544_;
v___y_478_ = v___y_536_;
v___y_479_ = v_snd_531_;
v___y_480_ = v_struct_767_;
v___y_481_ = v___y_541_;
v___y_482_ = v_typeName_765_;
v___y_483_ = v___y_537_;
v___y_484_ = v_struct_770_;
v___y_485_ = v___y_540_;
v___y_486_ = v___x_771_;
goto v___jp_469_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_eq(v_idx_766_, v_idx_769_);
lean_dec(v_idx_769_);
v___y_470_ = v___y_539_;
v___y_471_ = v___y_546_;
v___y_472_ = v___y_543_;
v___y_473_ = v_idx_766_;
v___y_474_ = v___y_538_;
v___y_475_ = v___y_542_;
v___y_476_ = v___y_545_;
v___y_477_ = v___y_544_;
v___y_478_ = v___y_536_;
v___y_479_ = v_snd_531_;
v___y_480_ = v_struct_767_;
v___y_481_ = v___y_541_;
v___y_482_ = v_typeName_765_;
v___y_483_ = v___y_537_;
v___y_484_ = v_struct_770_;
v___y_485_ = v___y_540_;
v___y_486_ = v___x_772_;
goto v___jp_469_;
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec_ref_known(v_lhs_454_, 3);
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
v___x_773_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_773_);
v___x_775_ = v___x_520_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
default: 
{
lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v_snd_531_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v___x_777_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_777_);
v___x_779_ = v___x_520_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
v___jp_781_:
{
if (v___y_782_ == 0)
{
lean_del_object(v___x_533_);
lean_del_object(v___x_528_);
v___y_536_ = v_a_456_;
v___y_537_ = v_a_458_;
v___y_538_ = v_a_459_;
v___y_539_ = v_a_460_;
v___y_540_ = v_a_461_;
v___y_541_ = v_a_462_;
v___y_542_ = v_a_463_;
v___y_543_ = v_a_464_;
v___y_544_ = v_a_465_;
v___y_545_ = v_a_466_;
v___y_546_ = v_a_467_;
goto v___jp_535_;
}
else
{
lean_object* v___x_783_; 
lean_inc_ref(v_lhs_454_);
v___x_783_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_454_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
lean_inc_ref(v_rhs_455_);
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_455_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
lean_inc(v_a_463_);
lean_inc_ref(v_a_462_);
lean_inc(v_a_461_);
lean_inc_ref(v_a_460_);
lean_inc(v_a_459_);
lean_inc(v_a_458_);
v___x_787_ = lean_grind_process_new_facts(v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_788_; 
lean_dec_ref_known(v___x_787_, 1);
v___x_788_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_784_, v_a_786_, v_a_458_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = lean_unbox(v_a_789_);
lean_dec(v_a_789_);
if (v___x_790_ == 0)
{
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_del_object(v___x_528_);
v___y_536_ = v_a_456_;
v___y_537_ = v_a_458_;
v___y_538_ = v_a_459_;
v___y_539_ = v_a_460_;
v___y_540_ = v_a_461_;
v___y_541_ = v_a_462_;
v___y_542_ = v_a_463_;
v___y_543_ = v_a_464_;
v___y_544_ = v_a_465_;
v___y_545_ = v_a_466_;
v___y_546_ = v_a_467_;
goto v___jp_535_;
}
else
{
lean_object* v___x_791_; 
lean_inc(v_a_786_);
lean_inc(v_a_784_);
v___x_791_ = l_Lean_Meta_Grind_hasSameType(v_a_784_, v_a_786_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; uint8_t v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = lean_unbox(v_a_792_);
lean_dec(v_a_792_);
if (v___x_793_ == 0)
{
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_del_object(v___x_528_);
v___y_536_ = v_a_456_;
v___y_537_ = v_a_458_;
v___y_538_ = v_a_459_;
v___y_539_ = v_a_460_;
v___y_540_ = v_a_461_;
v___y_541_ = v_a_462_;
v___y_542_ = v_a_463_;
v___y_543_ = v_a_464_;
v___y_544_ = v_a_465_;
v___y_545_ = v_a_466_;
v___y_546_ = v_a_467_;
goto v___jp_535_;
}
else
{
lean_object* v___x_794_; 
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
lean_inc(v_a_784_);
v___x_794_ = lean_infer_type(v_a_784_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_825_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_825_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_825_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_825_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_cache_799_; lean_object* v_varTypes_800_; lean_object* v_lhss_801_; lean_object* v_rhss_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_824_; 
v_cache_799_ = lean_ctor_get(v_snd_531_, 0);
v_varTypes_800_ = lean_ctor_get(v_snd_531_, 1);
v_lhss_801_ = lean_ctor_get(v_snd_531_, 2);
v_rhss_802_ = lean_ctor_get(v_snd_531_, 3);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_531_);
if (v_isSharedCheck_824_ == 0)
{
v___x_804_ = v_snd_531_;
v_isShared_805_ = v_isSharedCheck_824_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_rhss_802_);
lean_inc(v_lhss_801_);
lean_inc(v_varTypes_800_);
lean_inc(v_cache_799_);
lean_dec(v_snd_531_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_824_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_806_ = lean_array_get_size(v_varTypes_800_);
v___x_807_ = lean_nat_add(v___x_806_, v_a_456_);
v___x_808_ = lean_array_push(v_varTypes_800_, v_a_795_);
v___x_809_ = lean_array_push(v_lhss_801_, v_a_784_);
v___x_810_ = lean_array_push(v_rhss_802_, v_a_786_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 3, v___x_810_);
lean_ctor_set(v___x_804_, 2, v___x_809_);
lean_ctor_set(v___x_804_, 1, v___x_808_);
v___x_812_ = v___x_804_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_cache_799_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v___x_810_);
v___x_812_ = v_reuseFailAlloc_823_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_mkBVar(v___x_807_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_812_);
lean_ctor_set(v___x_533_, 0, v___x_813_);
v___x_815_ = v___x_533_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_812_);
v___x_815_ = v_reuseFailAlloc_822_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_815_);
v___x_817_ = v___x_528_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_817_);
v___x_819_ = v___x_797_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
v_a_826_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_794_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_794_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_834_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_791_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_791_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_842_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_788_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_788_);
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
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_850_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_787_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_787_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_784_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_858_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_785_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_785_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_866_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_783_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_783_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_882_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_517_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_517_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
v___jp_469_:
{
if (v___y_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v___y_484_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_473_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_480_, v___y_484_, v___y_478_, v___y_479_, v___y_483_, v___y_474_, v___y_470_, v___y_485_, v___y_481_, v___y_475_, v___y_472_, v___y_477_, v___y_476_, v___y_471_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
if (lean_obj_tag(v_a_490_) == 0)
{
lean_dec(v___y_482_);
lean_dec(v___y_473_);
return v___x_489_;
}
else
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_515_; 
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_489_, 0);
lean_dec(v_unused_516_);
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_515_;
goto v_resetjp_491_;
}
else
{
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_515_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_val_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_514_; 
v_val_494_ = lean_ctor_get(v_a_490_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_514_ == 0)
{
v___x_496_ = v_a_490_;
v_isShared_497_ = v_isSharedCheck_514_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_val_494_);
lean_dec(v_a_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_514_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_513_; 
v_fst_498_ = lean_ctor_get(v_val_494_, 0);
v_snd_499_ = lean_ctor_get(v_val_494_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_val_494_);
if (v_isSharedCheck_513_ == 0)
{
v___x_501_ = v_val_494_;
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snd_499_);
lean_inc(v_fst_498_);
lean_dec(v_val_494_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Lean_Expr_proj___override(v___y_482_, v___y_473_, v_fst_498_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_snd_499_);
v___x_505_ = v_reuseFailAlloc_512_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_505_);
v___x_507_ = v___x_496_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_507_);
v___x_509_ = v___x_492_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
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
lean_dec(v___y_482_);
lean_dec(v___y_473_);
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object* v_lhs_890_, lean_object* v_rhs_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_lhs_890_, v_rhs_891_);
if (v___x_905_ == 0)
{
lean_object* v_cache_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_cache_906_ = lean_ctor_get(v_a_893_, 0);
lean_inc_ref(v_rhs_891_);
lean_inc_ref(v_lhs_890_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_lhs_890_);
lean_ctor_set(v___x_907_, 1, v_rhs_891_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_906_, v___x_907_);
if (lean_obj_tag(v___x_908_) == 1)
{
lean_object* v_val_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref_known(v___x_907_, 2);
lean_dec_ref(v_rhs_891_);
lean_dec_ref(v_lhs_890_);
v_val_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_918_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_val_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_918_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_val_909_);
lean_ctor_set(v___x_913_, 1, v_a_893_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v___x_908_);
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_890_, v_rhs_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
if (lean_obj_tag(v_a_920_) == 0)
{
lean_dec_ref_known(v___x_907_, 2);
return v___x_919_;
}
else
{
lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_956_; 
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_919_, 0);
lean_dec(v_unused_957_);
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_956_;
goto v_resetjp_921_;
}
else
{
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_956_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_val_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_955_; 
v_val_924_ = lean_ctor_get(v_a_920_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_a_920_);
if (v_isSharedCheck_955_ == 0)
{
v___x_926_ = v_a_920_;
v_isShared_927_ = v_isSharedCheck_955_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_val_924_);
lean_dec(v_a_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_955_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_snd_928_; lean_object* v_fst_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_954_; 
v_snd_928_ = lean_ctor_get(v_val_924_, 1);
v_fst_929_ = lean_ctor_get(v_val_924_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_val_924_);
if (v_isSharedCheck_954_ == 0)
{
v___x_931_ = v_val_924_;
v_isShared_932_ = v_isSharedCheck_954_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_snd_928_);
lean_inc(v_fst_929_);
lean_dec(v_val_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_954_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_cache_933_; lean_object* v_varTypes_934_; lean_object* v_lhss_935_; lean_object* v_rhss_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_953_; 
v_cache_933_ = lean_ctor_get(v_snd_928_, 0);
v_varTypes_934_ = lean_ctor_get(v_snd_928_, 1);
v_lhss_935_ = lean_ctor_get(v_snd_928_, 2);
v_rhss_936_ = lean_ctor_get(v_snd_928_, 3);
v_isSharedCheck_953_ = !lean_is_exclusive(v_snd_928_);
if (v_isSharedCheck_953_ == 0)
{
v___x_938_ = v_snd_928_;
v_isShared_939_ = v_isSharedCheck_953_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_rhss_936_);
lean_inc(v_lhss_935_);
lean_inc(v_varTypes_934_);
lean_inc(v_cache_933_);
lean_dec(v_snd_928_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_953_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
lean_inc(v_fst_929_);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_933_, v___x_907_, v_fst_929_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_varTypes_934_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_lhss_935_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_rhss_936_);
v___x_942_ = v_reuseFailAlloc_952_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_942_);
v___x_944_ = v___x_931_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_fst_929_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_942_);
v___x_944_ = v_reuseFailAlloc_951_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_944_);
v___x_946_ = v___x_926_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_946_);
v___x_948_ = v___x_922_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
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
lean_dec_ref_known(v___x_907_, 2);
return v___x_919_;
}
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v_rhs_891_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_lhs_890_);
lean_ctor_set(v___x_958_, 1, v_a_893_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object* v_lhs_961_, lean_object* v_rhs_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_961_, v_rhs_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec(v_a_965_);
lean_dec(v_a_963_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object* v_lhs_977_, lean_object* v_rhs_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_977_, v_rhs_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_979_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(lean_object* v_00_u03b2_993_, lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_994_, v_a_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(lean_object* v_00_u03b2_997_, lean_object* v_m_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(v_00_u03b2_997_, v_m_998_, v_a_999_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_m_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object* v_00_u03b2_1001_, lean_object* v_m_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_1002_, v_a_1003_, v_b_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(lean_object* v_00_u03b2_1006_, lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_1007_, v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1010_, lean_object* v_a_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(v_00_u03b2_1010_, v_a_1011_, v_x_1012_);
lean_dec(v_x_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object* v_00_u03b2_1014_, lean_object* v_a_1015_, lean_object* v_x_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_1015_, v_x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1018_, lean_object* v_a_1019_, lean_object* v_x_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_1018_, v_a_1019_, v_x_1020_);
lean_dec(v_x_1020_);
lean_dec_ref(v_a_1019_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(lean_object* v_00_u03b2_1023_, lean_object* v_data_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_data_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(lean_object* v_00_u03b2_1026_, lean_object* v_a_1027_, lean_object* v_b_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_1027_, v_b_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1031_, lean_object* v_i_1032_, lean_object* v_source_1033_, lean_object* v_target_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v_i_1032_, v_source_1033_, v_target_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1037_, v_x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_unsigned_to_nat(16u);
v___x_1042_ = lean_mk_array(v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2));
v___x_1049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
v___x_1050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1048_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
lean_ctor_set(v___x_1050_, 3, v___x_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object* v_lhs_1058_, lean_object* v_rhs_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Sym_shareCommon(v_lhs_1058_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l_Lean_Meta_Sym_shareCommon(v_rhs_1059_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
v___x_1077_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_1072_, v_a_1074_, v___x_1075_, v___x_1076_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1147_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1147_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1147_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1142_; 
v_val_1082_ = lean_ctor_get(v_a_1078_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_a_1078_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1084_ = v_a_1078_;
v_isShared_1085_ = v_isSharedCheck_1142_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_val_1082_);
lean_dec(v_a_1078_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1142_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_snd_1086_; lean_object* v_fst_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1141_; 
v_snd_1086_ = lean_ctor_get(v_val_1082_, 1);
v_fst_1087_ = lean_ctor_get(v_val_1082_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_val_1082_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1089_ = v_val_1082_;
v_isShared_1090_ = v_isSharedCheck_1141_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snd_1086_);
lean_inc(v_fst_1087_);
lean_dec(v_val_1082_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1141_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_varTypes_1091_; lean_object* v_lhss_1092_; lean_object* v_rhss_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_varTypes_1091_ = lean_ctor_get(v_snd_1086_, 1);
lean_inc_ref(v_varTypes_1091_);
v_lhss_1092_ = lean_ctor_get(v_snd_1086_, 2);
lean_inc_ref(v_lhss_1092_);
v_rhss_1093_ = lean_ctor_get(v_snd_1086_, 3);
lean_inc_ref(v_rhss_1093_);
lean_dec(v_snd_1086_);
v___x_1094_ = lean_array_get_size(v_lhss_1092_);
v___x_1095_ = lean_nat_dec_eq(v___x_1094_, v___x_1075_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1080_);
v___x_1096_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_1091_, v_fst_1087_);
lean_dec_ref(v_varTypes_1091_);
lean_inc(v_a_1069_);
lean_inc_ref(v_a_1068_);
lean_inc(v_a_1067_);
lean_inc_ref(v_a_1066_);
lean_inc_ref(v___x_1096_);
v___x_1097_ = lean_infer_type(v___x_1096_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_n(v_a_1098_, 2);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l_Lean_Meta_getLevel(v_a_1098_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1120_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1120_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1120_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7));
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1100_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_Expr_const___override(v___x_1104_, v___x_1106_);
v___x_1108_ = l_Lean_mkAppB(v___x_1107_, v_a_1098_, v___x_1096_);
lean_inc_ref(v___x_1108_);
v___x_1109_ = l_Lean_mkAppN(v___x_1108_, v_lhss_1092_);
lean_dec_ref(v_lhss_1092_);
v___x_1110_ = l_Lean_mkAppN(v___x_1108_, v_rhss_1093_);
lean_dec_ref(v_rhss_1093_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v___x_1110_);
lean_ctor_set(v___x_1089_, 0, v___x_1109_);
v___x_1112_ = v___x_1089_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1112_);
v___x_1114_ = v___x_1084_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1114_);
v___x_1116_ = v___x_1102_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1098_);
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_rhss_1093_);
lean_dec_ref(v_lhss_1092_);
lean_del_object(v___x_1089_);
lean_del_object(v___x_1084_);
v_a_1121_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1099_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1099_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_rhss_1093_);
lean_dec_ref(v_lhss_1092_);
lean_del_object(v___x_1089_);
lean_del_object(v___x_1084_);
v_a_1129_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1097_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1097_);
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
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec_ref(v_rhss_1093_);
lean_dec_ref(v_lhss_1092_);
lean_dec_ref(v_varTypes_1091_);
lean_del_object(v___x_1089_);
lean_dec(v_fst_1087_);
lean_del_object(v___x_1084_);
v___x_1137_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1137_);
v___x_1139_ = v___x_1080_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
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
else
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
lean_dec(v_a_1078_);
v___x_1143_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1143_);
v___x_1145_ = v___x_1080_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
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
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_a_1148_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1077_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1077_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_a_1072_);
v_a_1156_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1073_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1073_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_rhs_1059_);
v_a_1164_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1071_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1071_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object* v_lhs_1172_, lean_object* v_rhs_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_1172_, v_rhs_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec(v_a_1174_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(lean_object* v_msgData_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v___x_1194_; lean_object* v_mctx_1195_; lean_object* v_lctx_1196_; lean_object* v_options_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_st_ref_get(v___y_1188_);
v_mctx_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc_ref(v_mctx_1195_);
lean_dec(v___x_1194_);
v_lctx_1196_ = lean_ctor_get(v___y_1187_, 2);
v_options_1197_ = lean_ctor_get(v___y_1189_, 2);
lean_inc_ref(v_options_1197_);
lean_inc_ref(v_lctx_1196_);
v___x_1198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1198_, 0, v_env_1193_);
lean_ctor_set(v___x_1198_, 1, v_mctx_1195_);
lean_ctor_set(v___x_1198_, 2, v_lctx_1196_);
lean_ctor_set(v___x_1198_, 3, v_options_1197_);
v___x_1199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_msgData_1186_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(lean_object* v_msgData_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1208_; double v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_float_of_nat(v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object* v_cls_1213_, lean_object* v_msg_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_ref_1220_; lean_object* v___x_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1266_; 
v_ref_1220_ = lean_ctor_get(v___y_1217_, 5);
v___x_1221_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1266_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1266_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v_traceState_1227_; lean_object* v_env_1228_; lean_object* v_nextMacroScope_1229_; lean_object* v_ngen_1230_; lean_object* v_auxDeclNGen_1231_; lean_object* v_cache_1232_; lean_object* v_messages_1233_; lean_object* v_infoState_1234_; lean_object* v_snapshotTasks_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1265_; 
v___x_1226_ = lean_st_ref_take(v___y_1218_);
v_traceState_1227_ = lean_ctor_get(v___x_1226_, 4);
v_env_1228_ = lean_ctor_get(v___x_1226_, 0);
v_nextMacroScope_1229_ = lean_ctor_get(v___x_1226_, 1);
v_ngen_1230_ = lean_ctor_get(v___x_1226_, 2);
v_auxDeclNGen_1231_ = lean_ctor_get(v___x_1226_, 3);
v_cache_1232_ = lean_ctor_get(v___x_1226_, 5);
v_messages_1233_ = lean_ctor_get(v___x_1226_, 6);
v_infoState_1234_ = lean_ctor_get(v___x_1226_, 7);
v_snapshotTasks_1235_ = lean_ctor_get(v___x_1226_, 8);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1237_ = v___x_1226_;
v_isShared_1238_ = v_isSharedCheck_1265_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snapshotTasks_1235_);
lean_inc(v_infoState_1234_);
lean_inc(v_messages_1233_);
lean_inc(v_cache_1232_);
lean_inc(v_traceState_1227_);
lean_inc(v_auxDeclNGen_1231_);
lean_inc(v_ngen_1230_);
lean_inc(v_nextMacroScope_1229_);
lean_inc(v_env_1228_);
lean_dec(v___x_1226_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1265_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint64_t v_tid_1239_; lean_object* v_traces_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1264_; 
v_tid_1239_ = lean_ctor_get_uint64(v_traceState_1227_, sizeof(void*)*1);
v_traces_1240_ = lean_ctor_get(v_traceState_1227_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_traceState_1227_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1242_ = v_traceState_1227_;
v_isShared_1243_ = v_isSharedCheck_1264_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_traces_1240_);
lean_dec(v_traceState_1227_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1264_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; double v___x_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
v___x_1246_ = 0;
v___x_1247_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1));
v___x_1248_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1248_, 0, v_cls_1213_);
lean_ctor_set(v___x_1248_, 1, v___x_1244_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
lean_ctor_set_float(v___x_1248_, sizeof(void*)*3, v___x_1245_);
lean_ctor_set_float(v___x_1248_, sizeof(void*)*3 + 8, v___x_1245_);
lean_ctor_set_uint8(v___x_1248_, sizeof(void*)*3 + 16, v___x_1246_);
v___x_1249_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2));
v___x_1250_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v_a_1222_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
lean_inc(v_ref_1220_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_ref_1220_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_PersistentArray_push___redArg(v_traces_1240_, v___x_1251_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1252_);
v___x_1254_ = v___x_1242_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1252_);
lean_ctor_set_uint64(v_reuseFailAlloc_1263_, sizeof(void*)*1, v_tid_1239_);
v___x_1254_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 4, v___x_1254_);
v___x_1256_ = v___x_1237_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_env_1228_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_nextMacroScope_1229_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_ngen_1230_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_auxDeclNGen_1231_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1262_, 5, v_cache_1232_);
lean_ctor_set(v_reuseFailAlloc_1262_, 6, v_messages_1233_);
lean_ctor_set(v_reuseFailAlloc_1262_, 7, v_infoState_1234_);
lean_ctor_set(v_reuseFailAlloc_1262_, 8, v_snapshotTasks_1235_);
v___x_1256_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1257_ = lean_st_ref_set(v___y_1218_, v___x_1256_);
v___x_1258_ = lean_box(0);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1258_);
v___x_1260_ = v___x_1224_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object* v_cls_1267_, lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1267_, v_msg_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5));
v___x_1287_ = l_Lean_Name_append(v___x_1286_, v___x_1285_);
return v___x_1287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object* v_lhs_u2080_1297_, lean_object* v_rhs_u2080_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_1297_, v_rhs_u2080_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1435_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1435_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1435_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
if (lean_obj_tag(v_a_1311_) == 1)
{
lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1430_; 
lean_del_object(v___x_1313_);
v_val_1315_ = lean_ctor_get(v_a_1311_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_a_1311_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1317_ = v_a_1311_;
v_isShared_1318_ = v_isSharedCheck_1430_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_dec(v_a_1311_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1430_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1429_; 
v_fst_1319_ = lean_ctor_get(v_val_1315_, 0);
v_snd_1320_ = lean_ctor_get(v_val_1315_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_val_1315_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1322_ = v_val_1315_;
v_isShared_1323_ = v_isSharedCheck_1429_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1320_);
lean_inc(v_fst_1319_);
lean_dec(v_val_1315_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1429_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v_options_1403_; uint8_t v_hasTrace_1404_; 
v_options_1403_ = lean_ctor_get(v_a_1307_, 2);
v_hasTrace_1404_ = lean_ctor_get_uint8(v_options_1403_, sizeof(void*)*1);
if (v_hasTrace_1404_ == 0)
{
lean_del_object(v___x_1322_);
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
v___y_1328_ = v_a_1302_;
v___y_1329_ = v_a_1303_;
v___y_1330_ = v_a_1304_;
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
v___y_1334_ = v_a_1308_;
goto v___jp_1324_;
}
else
{
lean_object* v_inheritedTraceOptions_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_inheritedTraceOptions_1405_ = lean_ctor_get(v_a_1307_, 13);
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1405_, v_options_1403_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_del_object(v___x_1322_);
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
v___y_1328_ = v_a_1302_;
v___y_1329_ = v_a_1303_;
v___y_1330_ = v_a_1304_;
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
v___y_1334_ = v_a_1308_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
lean_inc(v_fst_1319_);
v___x_1410_ = l_Lean_MessageData_ofExpr(v_fst_1319_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 7);
lean_ctor_set(v___x_1322_, 1, v___x_1410_);
lean_ctor_set(v___x_1322_, 0, v___x_1409_);
v___x_1412_ = v___x_1322_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
lean_inc(v_snd_1320_);
v___x_1415_ = l_Lean_MessageData_ofExpr(v_snd_1320_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_1406_, v___x_1418_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_dec_ref_known(v___x_1419_, 1);
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
v___y_1328_ = v_a_1302_;
v___y_1329_ = v_a_1303_;
v___y_1330_ = v_a_1304_;
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
v___y_1334_ = v_a_1308_;
goto v___jp_1324_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_snd_1320_);
lean_dec(v_fst_1319_);
lean_del_object(v___x_1317_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
v___jp_1324_:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_1319_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_1320_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc(v___y_1325_);
v___x_1339_ = lean_grind_process_new_facts(v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref_known(v___x_1339_, 1);
v___x_1340_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1336_, v_a_1338_, v___y_1325_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1370_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1370_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1370_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_unbox(v_a_1341_);
lean_dec(v_a_1341_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec(v_a_1338_);
lean_dec(v_a_1336_);
lean_del_object(v___x_1317_);
v___x_1346_ = lean_box(0);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1346_);
v___x_1348_ = v___x_1343_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_object* v___x_1350_; 
lean_del_object(v___x_1343_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc(v___y_1325_);
v___x_1350_ = lean_grind_mk_eq_proof(v_a_1336_, v_a_1338_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1361_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_a_1351_);
v___x_1356_ = v___x_1317_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1356_);
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1317_);
v_a_1362_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1350_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1350_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1338_);
lean_dec(v_a_1336_);
lean_del_object(v___x_1317_);
v_a_1371_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1340_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1340_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1338_);
lean_dec(v_a_1336_);
lean_del_object(v___x_1317_);
v_a_1379_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1339_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1339_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_a_1336_);
lean_del_object(v___x_1317_);
v_a_1387_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1337_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1337_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_snd_1320_);
lean_del_object(v___x_1317_);
v_a_1395_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1335_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1335_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec(v_a_1311_);
v___x_1431_ = lean_box(0);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1431_);
v___x_1433_ = v___x_1313_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1310_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1310_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object* v_lhs_u2080_1444_, lean_object* v_rhs_u2080_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_lhs_u2080_1444_, v_rhs_u2080_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec(v_a_1446_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object* v_cls_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1458_, v_msg_1459_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object* v_cls_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_1472_, v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec(v___y_1474_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object* v_lhs_1486_, lean_object* v_rhs_1487_, uint8_t v_abstract_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1486_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1487_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
lean_inc_ref(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc(v___y_1489_);
v___x_1504_ = lean_grind_process_new_facts(v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; 
lean_dec_ref_known(v___x_1504_, 1);
v___x_1505_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1501_, v_a_1503_, v___y_1489_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1534_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1534_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1534_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_unbox(v_a_1506_);
lean_dec(v_a_1506_);
if (v___x_1510_ == 0)
{
if (v_abstract_1488_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1501_);
v___x_1511_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
else
{
lean_object* v___x_1515_; 
lean_del_object(v___x_1508_);
v___x_1515_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_a_1501_, v_a_1503_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1515_;
}
}
else
{
lean_object* v___x_1516_; 
lean_del_object(v___x_1508_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
lean_inc_ref(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc(v___y_1489_);
v___x_1516_ = lean_grind_mk_eq_proof(v_a_1501_, v_a_1503_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_a_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1516_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1516_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1501_);
v_a_1535_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1505_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1505_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1501_);
v_a_1543_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1504_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1504_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_a_1501_);
v_a_1551_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1502_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1502_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_rhs_1487_);
v_a_1559_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1500_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1500_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object* v_lhs_1567_, lean_object* v_rhs_1568_, lean_object* v_abstract_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_abstract_boxed_1581_; lean_object* v_res_1582_; 
v_abstract_boxed_1581_ = lean_unbox(v_abstract_1569_);
v_res_1582_ = l_Lean_Meta_Grind_proveEq_x3f___lam__0(v_lhs_1567_, v_rhs_1568_, v_abstract_boxed_1581_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec(v___y_1570_);
return v_res_1582_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l_Lean_Meta_Grind_proveEq_x3f___closed__0));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object* v_lhs_1586_, lean_object* v_rhs_1587_, uint8_t v_abstract_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_options_1600_; lean_object* v_inheritedTraceOptions_1601_; uint8_t v_hasTrace_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; 
v_options_1600_ = lean_ctor_get(v_a_1597_, 2);
v_inheritedTraceOptions_1601_ = lean_ctor_get(v_a_1597_, 13);
v_hasTrace_1602_ = lean_ctor_get_uint8(v_options_1600_, sizeof(void*)*1);
v___x_1603_ = lean_box(v_abstract_1588_);
lean_inc_ref(v_rhs_1587_);
lean_inc_ref(v_lhs_1586_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed), 14, 3);
lean_closure_set(v___f_1604_, 0, v_lhs_1586_);
lean_closure_set(v___f_1604_, 1, v_rhs_1587_);
lean_closure_set(v___f_1604_, 2, v___x_1603_);
if (v_hasTrace_1602_ == 0)
{
v___y_1668_ = v_a_1589_;
v___y_1669_ = v_a_1590_;
v___y_1670_ = v_a_1591_;
v___y_1671_ = v_a_1592_;
v___y_1672_ = v_a_1593_;
v___y_1673_ = v_a_1594_;
v___y_1674_ = v_a_1595_;
v___y_1675_ = v_a_1596_;
v___y_1676_ = v_a_1597_;
v___y_1677_ = v_a_1598_;
goto v___jp_1667_;
}
else
{
lean_object* v_cls_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_cls_1701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1703_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1601_, v_options_1600_, v___x_1702_);
if (v___x_1703_ == 0)
{
v___y_1668_ = v_a_1589_;
v___y_1669_ = v_a_1590_;
v___y_1670_ = v_a_1591_;
v___y_1671_ = v_a_1592_;
v___y_1672_ = v_a_1593_;
v___y_1673_ = v_a_1594_;
v___y_1674_ = v_a_1595_;
v___y_1675_ = v_a_1596_;
v___y_1676_ = v_a_1597_;
v___y_1677_ = v_a_1598_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1704_ = lean_obj_once(&l_Lean_Meta_Grind_proveEq_x3f___closed__1, &l_Lean_Meta_Grind_proveEq_x3f___closed__1_once, _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1);
lean_inc_ref(v_lhs_1586_);
v___x_1705_ = l_Lean_MessageData_ofExpr(v_lhs_1586_);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
lean_inc_ref(v_rhs_1587_);
v___x_1709_ = l_Lean_MessageData_ofExpr(v_rhs_1587_);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1701_, v___x_1712_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec_ref_known(v___x_1713_, 1);
v___y_1668_ = v_a_1589_;
v___y_1669_ = v_a_1590_;
v___y_1670_ = v_a_1591_;
v___y_1671_ = v_a_1592_;
v___y_1672_ = v_a_1593_;
v___y_1673_ = v_a_1594_;
v___y_1674_ = v_a_1595_;
v___y_1675_ = v_a_1596_;
v___y_1676_ = v_a_1597_;
v___y_1677_ = v_a_1598_;
goto v___jp_1667_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v___f_1604_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
v___jp_1605_:
{
if (lean_obj_tag(v___y_1616_) == 0)
{
lean_object* v_a_1617_; uint8_t v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___y_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___y_1616_, 1);
v___x_1618_ = lean_unbox(v_a_1617_);
lean_dec(v_a_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v___x_1619_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1604_, v___y_1610_, v___y_1613_, v___y_1608_, v___y_1611_, v___y_1615_, v___y_1609_, v___y_1607_, v___y_1614_, v___y_1606_, v___y_1612_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; 
lean_dec_ref(v___f_1604_);
v___x_1620_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1586_, v_rhs_1587_, v___y_1610_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1650_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1650_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1650_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_unbox(v_a_1621_);
lean_dec(v_a_1621_);
if (v___x_1625_ == 0)
{
if (v_abstract_1588_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v___x_1626_ = lean_box(0);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1623_);
v___x_1630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 13, 2);
lean_closure_set(v___x_1630_, 0, v_lhs_1586_);
lean_closure_set(v___x_1630_, 1, v_rhs_1587_);
v___x_1631_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___x_1630_, v___y_1610_, v___y_1613_, v___y_1608_, v___y_1611_, v___y_1615_, v___y_1609_, v___y_1607_, v___y_1614_, v___y_1606_, v___y_1612_);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1632_; 
lean_del_object(v___x_1623_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1608_);
lean_inc(v___y_1613_);
lean_inc(v___y_1610_);
v___x_1632_ = lean_grind_mk_eq_proof(v_lhs_1586_, v_rhs_1587_, v___y_1610_, v___y_1613_, v___y_1608_, v___y_1611_, v___y_1615_, v___y_1609_, v___y_1607_, v___y_1614_, v___y_1606_, v___y_1612_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1641_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_a_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1632_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1632_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1651_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1620_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1620_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v___f_1604_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1659_ = lean_ctor_get(v___y_1616_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___y_1616_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___y_1616_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___y_1616_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
v___jp_1667_:
{
lean_object* v___x_1678_; 
lean_inc_ref(v_rhs_1587_);
lean_inc_ref(v_lhs_1586_);
v___x_1678_ = l_Lean_Meta_Grind_hasSameType(v_lhs_1586_, v_rhs_1587_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1692_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1692_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1692_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_unbox(v_a_1679_);
lean_dec(v_a_1679_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_dec_ref(v___f_1604_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v___x_1684_ = lean_box(0);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1684_);
v___x_1686_ = v___x_1681_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
else
{
lean_object* v___x_1688_; 
lean_del_object(v___x_1681_);
v___x_1688_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1586_, v___y_1668_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
v___x_1690_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1690_ == 0)
{
v___y_1606_ = v___y_1676_;
v___y_1607_ = v___y_1674_;
v___y_1608_ = v___y_1670_;
v___y_1609_ = v___y_1673_;
v___y_1610_ = v___y_1668_;
v___y_1611_ = v___y_1671_;
v___y_1612_ = v___y_1677_;
v___y_1613_ = v___y_1669_;
v___y_1614_ = v___y_1675_;
v___y_1615_ = v___y_1672_;
v___y_1616_ = v___x_1688_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1688_, 1);
v___x_1691_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1587_, v___y_1668_);
v___y_1606_ = v___y_1676_;
v___y_1607_ = v___y_1674_;
v___y_1608_ = v___y_1670_;
v___y_1609_ = v___y_1673_;
v___y_1610_ = v___y_1668_;
v___y_1611_ = v___y_1671_;
v___y_1612_ = v___y_1677_;
v___y_1613_ = v___y_1669_;
v___y_1614_ = v___y_1675_;
v___y_1615_ = v___y_1672_;
v___y_1616_ = v___x_1691_;
goto v___jp_1605_;
}
}
else
{
v___y_1606_ = v___y_1676_;
v___y_1607_ = v___y_1674_;
v___y_1608_ = v___y_1670_;
v___y_1609_ = v___y_1673_;
v___y_1610_ = v___y_1668_;
v___y_1611_ = v___y_1671_;
v___y_1612_ = v___y_1677_;
v___y_1613_ = v___y_1669_;
v___y_1614_ = v___y_1675_;
v___y_1615_ = v___y_1672_;
v___y_1616_ = v___x_1688_;
goto v___jp_1605_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v___f_1604_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1693_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1678_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1678_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object* v_lhs_1722_, lean_object* v_rhs_1723_, lean_object* v_abstract_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
uint8_t v_abstract_boxed_1736_; lean_object* v_res_1737_; 
v_abstract_boxed_1736_ = lean_unbox(v_abstract_1724_);
v_res_1737_ = l_Lean_Meta_Grind_proveEq_x3f(v_lhs_1722_, v_rhs_1723_, v_abstract_boxed_1736_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec(v_a_1725_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object* v_lhs_1738_, lean_object* v_rhs_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1738_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1744_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc(v___y_1740_);
v___x_1755_ = lean_grind_process_new_facts(v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; 
lean_dec_ref_known(v___x_1755_, 1);
v___x_1756_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1752_, v_a_1754_, v___y_1740_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1784_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1784_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1784_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_unbox(v_a_1757_);
lean_dec(v_a_1757_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec(v_a_1754_);
lean_dec(v_a_1752_);
v___x_1762_ = lean_box(0);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v___x_1766_; 
lean_del_object(v___x_1759_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1744_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc(v___y_1740_);
v___x_1766_ = lean_grind_mk_heq_proof(v_a_1752_, v_a_1754_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1775_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_a_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1771_);
v___x_1773_ = v___x_1769_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1766_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1766_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_a_1754_);
lean_dec(v_a_1752_);
v_a_1785_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1756_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1756_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1754_);
lean_dec(v_a_1752_);
v_a_1793_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1755_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1755_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1752_);
v_a_1801_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1753_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1753_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_rhs_1739_);
v_a_1809_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1751_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1751_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object* v_lhs_1817_, lean_object* v_rhs_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(v_lhs_1817_, v_rhs_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec(v___y_1819_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object* v_lhs_1831_, lean_object* v_rhs_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___f_1844_; lean_object* v___y_1846_; lean_object* v___x_1895_; 
lean_inc_ref(v_rhs_1832_);
lean_inc_ref(v_lhs_1831_);
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1844_, 0, v_lhs_1831_);
lean_closure_set(v___f_1844_, 1, v_rhs_1832_);
v___x_1895_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1831_, v_a_1833_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
v___x_1897_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
if (v___x_1897_ == 0)
{
v___y_1846_ = v___x_1895_;
goto v___jp_1845_;
}
else
{
lean_object* v___x_1898_; 
lean_dec_ref_known(v___x_1895_, 1);
v___x_1898_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1832_, v_a_1833_);
v___y_1846_ = v___x_1898_;
goto v___jp_1845_;
}
}
else
{
v___y_1846_ = v___x_1895_;
goto v___jp_1845_;
}
v___jp_1845_:
{
if (lean_obj_tag(v___y_1846_) == 0)
{
lean_object* v_a_1847_; uint8_t v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___y_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___y_1846_, 1);
v___x_1848_ = lean_unbox(v_a_1847_);
lean_dec(v_a_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref(v_rhs_1832_);
lean_dec_ref(v_lhs_1831_);
v___x_1849_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1844_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; 
lean_dec_ref(v___f_1844_);
v___x_1850_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1831_, v_rhs_1832_, v_a_1833_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1878_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1878_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1878_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_unbox(v_a_1851_);
lean_dec(v_a_1851_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec_ref(v_rhs_1832_);
lean_dec_ref(v_lhs_1831_);
v___x_1856_ = lean_box(0);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1856_);
v___x_1858_ = v___x_1853_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
lean_object* v___x_1860_; 
lean_del_object(v___x_1853_);
lean_inc(v_a_1842_);
lean_inc_ref(v_a_1841_);
lean_inc(v_a_1840_);
lean_inc_ref(v_a_1839_);
lean_inc(v_a_1838_);
lean_inc_ref(v_a_1837_);
lean_inc(v_a_1836_);
lean_inc_ref(v_a_1835_);
lean_inc(v_a_1834_);
lean_inc(v_a_1833_);
v___x_1860_ = lean_grind_mk_heq_proof(v_lhs_1831_, v_rhs_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1860_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1860_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_rhs_1832_);
lean_dec_ref(v_lhs_1831_);
v_a_1879_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1850_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1850_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v___f_1844_);
lean_dec_ref(v_rhs_1832_);
lean_dec_ref(v_lhs_1831_);
v_a_1887_ = lean_ctor_get(v___y_1846_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___y_1846_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___y_1846_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object* v_lhs_1899_, lean_object* v_rhs_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Meta_Grind_proveHEq_x3f(v_lhs_1899_, v_rhs_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec(v_a_1901_);
return v_res_1912_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
}
#ifdef __cplusplus
}
#endif
