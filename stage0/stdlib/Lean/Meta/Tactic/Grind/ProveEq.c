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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "abstractFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(5, 46, 159, 125, 153, 141, 125, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8_value;
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
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
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
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_30_, v___y_38_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(lean_object* v_e_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(v_e_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec(v___y_44_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(lean_object* v_e_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_56_, v_a_57_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_100_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_100_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_100_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_100_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint8_t v___x_73_; 
v___x_73_ = lean_unbox(v_a_69_);
lean_dec(v_a_69_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v_a_75_; lean_object* v___x_76_; 
lean_del_object(v___x_71_);
v___x_74_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_56_, v_a_64_);
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref(v___x_74_);
v___x_76_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_75_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_n(v_a_77_, 2);
lean_dec_ref_known(v___x_76_, 1);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_box(0);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
lean_inc(v_a_60_);
lean_inc_ref(v_a_59_);
lean_inc(v_a_58_);
lean_inc(v_a_57_);
v___x_80_ = lean_grind_internalize(v_a_77_, v___x_78_, v___x_79_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_80_, 0);
lean_dec(v_unused_88_);
v___x_82_ = v___x_80_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_dec(v___x_80_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v_a_77_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_77_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_a_77_);
v_a_89_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_80_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_80_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
return v___x_76_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_e_56_);
v___x_98_ = v___x_71_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_e_56_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_e_56_);
v_a_101_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_68_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_68_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(lean_object* v_e_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_e_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec(v_a_110_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_dec_lt(v___x_125_, v_a_122_);
v___x_127_ = lean_box(v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_a_123_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_131_, v_a_132_);
lean_dec(v_a_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_135_, v_a_136_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec(v_a_151_);
lean_dec(v_a_149_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_a_164_, v___x_177_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc(v_a_167_);
lean_inc(v_a_166_);
v___x_179_ = lean_apply_13(v_x_163_, v___x_178_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, lean_box(0));
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(lean_object* v_x_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(v_x_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec(v_a_183_);
lean_dec(v_a_181_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_object* v_00_u03b1_195_, lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_a_197_, v___x_210_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
lean_inc(v_a_200_);
lean_inc(v_a_199_);
v___x_212_ = lean_apply_13(v_x_196_, v___x_211_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, lean_box(0));
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(lean_object* v_00_u03b1_213_, lean_object* v_x_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(v_00_u03b1_213_, v_x_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec(v_a_217_);
lean_dec(v_a_215_);
return v_res_228_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2(void){
_start:
{
lean_object* v_i_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_i_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1));
v___x_234_ = lean_name_append_index_after(v___x_233_, v_i_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(lean_object* v_as_235_, size_t v_sz_236_, size_t v_i_237_, lean_object* v_b_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_lt(v_i_237_, v_sz_236_);
if (v___x_239_ == 0)
{
return v_b_238_;
}
else
{
lean_object* v_a_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; size_t v___x_244_; size_t v___x_245_; 
v_a_240_ = lean_array_uget_borrowed(v_as_235_, v_i_237_);
v___x_241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2);
v___x_242_ = 0;
lean_inc(v_a_240_);
v___x_243_ = l_Lean_mkLambda(v___x_241_, v___x_242_, v_a_240_, v_b_238_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_237_, v___x_244_);
v_i_237_ = v___x_245_;
v_b_238_ = v___x_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(lean_object* v_as_247_, lean_object* v_sz_248_, lean_object* v_i_249_, lean_object* v_b_250_){
_start:
{
size_t v_sz_boxed_251_; size_t v_i_boxed_252_; lean_object* v_res_253_; 
v_sz_boxed_251_ = lean_unbox_usize(v_sz_248_);
lean_dec(v_sz_248_);
v_i_boxed_252_ = lean_unbox_usize(v_i_249_);
lean_dec(v_i_249_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_as_247_, v_sz_boxed_251_, v_i_boxed_252_, v_b_250_);
lean_dec_ref(v_as_247_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(lean_object* v_varTypes_254_, lean_object* v_b_255_){
_start:
{
size_t v_sz_256_; size_t v___x_257_; lean_object* v___x_258_; 
v_sz_256_ = lean_array_size(v_varTypes_254_);
v___x_257_ = ((size_t)0ULL);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_varTypes_254_, v_sz_256_, v___x_257_, v_b_255_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(lean_object* v_varTypes_259_, lean_object* v_b_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_259_, v_b_260_);
lean_dec_ref(v_varTypes_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object* v_m_262_, lean_object* v_query_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
lean_object* v_zero_267_; uint8_t v_isZero_268_; 
v_zero_267_ = lean_unsigned_to_nat(0u);
v_isZero_268_ = lean_nat_dec_eq(v_x_265_, v_zero_267_);
if (v_isZero_268_ == 1)
{
lean_dec(v_x_266_);
lean_dec(v_x_265_);
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(2);
return v___x_269_;
}
else
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_val_270_ = lean_ctor_get(v_x_264_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v_x_264_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v_x_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_val_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_keyArray_278_; lean_object* v_valueArray_279_; lean_object* v___x_280_; uint8_t v_isSome_281_; 
v_keyArray_278_ = lean_ctor_get(v_m_262_, 1);
v_valueArray_279_ = lean_ctor_get(v_m_262_, 2);
v___x_280_ = lean_array_fget_borrowed(v_keyArray_278_, v_x_266_);
v_isSome_281_ = lean_noption_is_some(v___x_280_);
if (v_isSome_281_ == 0)
{
lean_dec(v_x_265_);
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_x_266_);
return v___x_282_;
}
else
{
lean_object* v_val_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_x_266_);
v_val_283_ = lean_ctor_get(v_x_264_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v_x_264_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_val_283_);
lean_dec(v_x_264_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_val_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_one_291_; lean_object* v_n_292_; lean_object* v___y_294_; 
v_one_291_ = lean_unsigned_to_nat(1u);
v_n_292_ = lean_nat_sub(v_x_265_, v_one_291_);
lean_dec(v_x_265_);
if (v_isSome_281_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v___x_302_; uint8_t v_isSome_303_; 
v___x_302_ = lean_array_fget_borrowed(v_valueArray_279_, v_x_266_);
v_isSome_303_ = lean_noption_is_some(v___x_302_);
if (v_isSome_303_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v_val_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v_fst_307_; lean_object* v_snd_308_; lean_object* v_val_309_; uint8_t v___y_311_; uint8_t v___x_318_; 
lean_inc(v___x_280_);
v_val_304_ = lean_noption_get(v___x_280_);
v_fst_305_ = lean_ctor_get(v_val_304_, 0);
lean_inc(v_fst_305_);
v_snd_306_ = lean_ctor_get(v_val_304_, 1);
lean_inc(v_snd_306_);
v_fst_307_ = lean_ctor_get(v_query_263_, 0);
v_snd_308_ = lean_ctor_get(v_query_263_, 1);
lean_inc(v___x_302_);
v_val_309_ = lean_noption_get(v___x_302_);
v___x_318_ = lean_expr_eqv(v_fst_305_, v_fst_307_);
lean_dec(v_fst_305_);
if (v___x_318_ == 0)
{
lean_dec(v_snd_306_);
v___y_311_ = v___x_318_;
goto v___jp_310_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_expr_eqv(v_snd_306_, v_snd_308_);
lean_dec(v_snd_306_);
v___y_311_ = v___x_319_;
goto v___jp_310_;
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
lean_dec(v_val_309_);
lean_dec(v_val_304_);
v___x_312_ = lean_array_get_size(v_keyArray_278_);
v___x_313_ = lean_nat_add(v_x_266_, v_one_291_);
lean_dec(v_x_266_);
v___x_314_ = lean_nat_dec_lt(v___x_313_, v___x_312_);
if (v___x_314_ == 0)
{
lean_dec(v___x_313_);
v_x_265_ = v_n_292_;
v_x_266_ = v_zero_267_;
goto _start;
}
else
{
v_x_265_ = v_n_292_;
v_x_266_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_317_; 
lean_dec(v_n_292_);
lean_dec(v_x_264_);
v___x_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_317_, 0, v_x_266_);
lean_ctor_set(v___x_317_, 1, v_val_304_);
lean_ctor_set(v___x_317_, 2, v_val_309_);
return v___x_317_;
}
}
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_array_get_size(v_keyArray_278_);
v___x_296_ = lean_nat_add(v_x_266_, v_one_291_);
lean_dec(v_x_266_);
v___x_297_ = lean_nat_dec_lt(v___x_296_, v___x_295_);
if (v___x_297_ == 0)
{
lean_dec(v___x_296_);
v_x_264_ = v___y_294_;
v_x_265_ = v_n_292_;
v_x_266_ = v_zero_267_;
goto _start;
}
else
{
v_x_264_ = v___y_294_;
v_x_265_ = v_n_292_;
v_x_266_ = v___x_296_;
goto _start;
}
}
v___jp_300_:
{
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_301_; 
lean_inc(v_x_266_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v_x_266_);
v___y_294_ = v___x_301_;
goto v___jp_293_;
}
else
{
v___y_294_ = v_x_264_;
goto v___jp_293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(lean_object* v_m_320_, lean_object* v_query_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_m_320_, v_query_321_, v_x_322_, v_x_323_, v_x_324_);
lean_dec_ref(v_query_321_);
lean_dec_ref(v_m_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object* v_m_326_, lean_object* v_query_327_){
_start:
{
lean_object* v_keyArray_328_; lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v_fold_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_keyArray_328_ = lean_ctor_get(v_m_326_, 1);
v_fst_329_ = lean_ctor_get(v_query_327_, 0);
v_snd_330_ = lean_ctor_get(v_query_327_, 1);
v___x_331_ = lean_array_get_size(v_keyArray_328_);
v___x_332_ = l_Lean_Expr_hash(v_fst_329_);
v___x_333_ = l_Lean_Expr_hash(v_snd_330_);
v___x_334_ = lean_uint64_mix_hash(v___x_332_, v___x_333_);
v___x_335_ = 32ULL;
v___x_336_ = lean_uint64_shift_right(v___x_334_, v___x_335_);
v_fold_337_ = lean_uint64_xor(v___x_334_, v___x_336_);
v___x_338_ = 16ULL;
v___x_339_ = lean_uint64_shift_right(v_fold_337_, v___x_338_);
v___x_340_ = lean_uint64_xor(v_fold_337_, v___x_339_);
v___x_341_ = lean_uint64_to_usize(v___x_340_);
v___x_342_ = lean_usize_of_nat(v___x_331_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_sub(v___x_342_, v___x_343_);
v___x_345_ = lean_usize_land(v___x_341_, v___x_344_);
v___x_346_ = lean_usize_to_nat(v___x_345_);
v___x_347_ = lean_box(0);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_m_326_, v_query_327_, v___x_347_, v___x_331_, v___x_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg___boxed(lean_object* v_m_349_, lean_object* v_query_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_349_, v_query_350_);
lean_dec_ref(v_query_350_);
lean_dec_ref(v_m_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(lean_object* v_m_352_, lean_object* v_query_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_352_, v_query_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_index_355_; lean_object* v_key_356_; lean_object* v_value_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
v_index_355_ = lean_ctor_get(v___x_354_, 0);
v_key_356_ = lean_ctor_get(v___x_354_, 1);
v_value_357_ = lean_ctor_get(v___x_354_, 2);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_354_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_value_357_);
lean_inc(v_key_356_);
lean_inc(v_index_355_);
lean_dec(v___x_354_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_index_355_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_key_356_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_value_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v___x_365_; 
lean_dec(v___x_354_);
v___x_365_ = lean_box(1);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(lean_object* v_m_366_, lean_object* v_query_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_m_366_, v_query_367_);
lean_dec_ref(v_query_367_);
lean_dec_ref(v_m_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(lean_object* v_m_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_m_369_, v_a_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_value_372_; lean_object* v___x_373_; 
v_value_372_ = lean_ctor_get(v___x_371_, 2);
lean_inc(v_value_372_);
lean_dec_ref_known(v___x_371_, 3);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_value_372_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_box(0);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(lean_object* v_m_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_375_, v_a_376_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_m_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg(lean_object* v_b_378_, lean_object* v_acc_379_, lean_object* v_i_380_){
_start:
{
lean_object* v___y_382_; lean_object* v_keyArray_390_; lean_object* v_valueArray_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_keyArray_390_ = lean_ctor_get(v_b_378_, 1);
v_valueArray_391_ = lean_ctor_get(v_b_378_, 2);
v___x_392_ = lean_array_get_size(v_keyArray_390_);
v___x_393_ = lean_nat_dec_lt(v_i_380_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_i_380_);
return v_acc_379_;
}
else
{
lean_object* v___x_394_; uint8_t v_isSome_395_; 
v___x_394_ = lean_array_fget_borrowed(v_keyArray_390_, v_i_380_);
v_isSome_395_ = lean_noption_is_some(v___x_394_);
if (v_isSome_395_ == 0)
{
goto v___jp_386_;
}
else
{
lean_object* v___x_396_; uint8_t v_isSome_397_; 
v___x_396_ = lean_array_fget_borrowed(v_valueArray_391_, v_i_380_);
v_isSome_397_ = lean_noption_is_some(v___x_396_);
if (v_isSome_397_ == 0)
{
goto v___jp_386_;
}
else
{
lean_object* v_val_398_; lean_object* v_val_399_; lean_object* v_i_401_; lean_object* v___x_406_; 
lean_inc(v___x_394_);
v_val_398_ = lean_noption_get(v___x_394_);
lean_inc(v___x_396_);
v_val_399_ = lean_noption_get(v___x_396_);
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_acc_379_, v_val_398_);
switch(lean_obj_tag(v___x_406_))
{
case 0:
{
lean_object* v_index_407_; lean_object* v_size_408_; lean_object* v___x_409_; 
v_index_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_index_407_);
lean_dec_ref_known(v___x_406_, 3);
v_size_408_ = lean_ctor_get(v_acc_379_, 0);
lean_inc(v_size_408_);
v___x_409_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_379_, v_size_408_, v_index_407_, v_val_398_, v_val_399_);
lean_dec(v_index_407_);
v___y_382_ = v___x_409_;
goto v___jp_381_;
}
case 1:
{
lean_object* v_index_410_; 
v_index_410_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_index_410_);
lean_dec_ref_known(v___x_406_, 1);
v_i_401_ = v_index_410_;
goto v___jp_400_;
}
default: 
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_379_, v___x_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_index_413_; 
v_index_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_index_413_);
lean_dec_ref_known(v___x_412_, 1);
v_i_401_ = v_index_413_;
goto v___jp_400_;
}
else
{
lean_dec(v_val_399_);
lean_dec(v_val_398_);
v___y_382_ = v_acc_379_;
goto v___jp_381_;
}
}
}
v___jp_400_:
{
lean_object* v_size_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_size_402_ = lean_ctor_get(v_acc_379_, 0);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_size_402_, v___x_403_);
v___x_405_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_379_, v___x_404_, v_i_401_, v_val_398_, v_val_399_);
lean_dec(v_i_401_);
v___y_382_ = v___x_405_;
goto v___jp_381_;
}
}
}
}
v___jp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_add(v_i_380_, v___x_383_);
lean_dec(v_i_380_);
v_acc_379_ = v___y_382_;
v_i_380_ = v___x_384_;
goto _start;
}
v___jp_386_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_i_380_, v___x_387_);
lean_dec(v_i_380_);
v_i_380_ = v___x_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_b_414_, lean_object* v_acc_415_, lean_object* v_i_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg(v_b_414_, v_acc_415_, v_i_416_);
lean_dec_ref(v_b_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg(lean_object* v_init_418_, lean_object* v_b_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg(v_b_419_, v_init_418_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg___boxed(lean_object* v_init_422_, lean_object* v_b_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg(v_init_422_, v_b_423_);
lean_dec_ref(v_b_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(lean_object* v_m_425_){
_start:
{
lean_object* v_keyArray_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_cellCount_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_target_433_; lean_object* v___x_434_; 
v_keyArray_426_ = lean_ctor_get(v_m_425_, 1);
v___x_427_ = lean_array_get_size(v_keyArray_426_);
v___x_428_ = lean_unsigned_to_nat(2u);
v_cellCount_429_ = lean_nat_mul(v___x_427_, v___x_428_);
v___x_430_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_429_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_429_);
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_429_);
v_target_433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_433_, 0, v___x_430_);
lean_ctor_set(v_target_433_, 1, v___x_431_);
lean_ctor_set(v_target_433_, 2, v___x_432_);
v___x_434_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg(v_target_433_, v_m_425_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg___boxed(lean_object* v_m_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(v_m_435_);
lean_dec_ref(v_m_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object* v_lhs_437_, lean_object* v_rhs_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; uint8_t v___y_469_; lean_object* v___x_500_; 
v___x_500_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_439_, v_a_440_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_860_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_860_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_860_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_860_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v___x_505_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v_val_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_859_; 
v_val_509_ = lean_ctor_get(v_a_501_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v_a_501_);
if (v_isSharedCheck_859_ == 0)
{
v___x_511_ = v_a_501_;
v_isShared_512_ = v_isSharedCheck_859_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_val_509_);
lean_dec(v_a_501_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_859_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_858_; 
v_fst_513_ = lean_ctor_get(v_val_509_, 0);
v_snd_514_ = lean_ctor_get(v_val_509_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_val_509_);
if (v_isSharedCheck_858_ == 0)
{
v___x_516_ = v_val_509_;
v_isShared_517_ = v_isSharedCheck_858_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_inc(v_fst_513_);
lean_dec(v_val_509_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_858_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; uint8_t v___x_764_; 
v___x_764_ = lean_unbox(v_fst_513_);
lean_dec(v_fst_513_);
if (v___x_764_ == 0)
{
lean_del_object(v___x_516_);
lean_del_object(v___x_511_);
v___y_519_ = v_a_439_;
v___y_520_ = v_a_441_;
v___y_521_ = v_a_442_;
v___y_522_ = v_a_443_;
v___y_523_ = v_a_444_;
v___y_524_ = v_a_445_;
v___y_525_ = v_a_446_;
v___y_526_ = v_a_447_;
v___y_527_ = v_a_448_;
v___y_528_ = v_a_449_;
v___y_529_ = v_a_450_;
goto v___jp_518_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = l_Lean_Expr_hasLooseBVars(v_lhs_437_);
if (v___x_765_ == 0)
{
uint8_t v___x_766_; 
v___x_766_ = l_Lean_Expr_hasLooseBVars(v_rhs_438_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_inc_ref(v_lhs_437_);
v___x_767_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_437_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
lean_inc_ref(v_rhs_438_);
v___x_769_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_438_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
lean_inc(v_a_450_);
lean_inc_ref(v_a_449_);
lean_inc(v_a_448_);
lean_inc_ref(v_a_447_);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc_ref(v_a_443_);
lean_inc(v_a_442_);
lean_inc(v_a_441_);
v___x_771_ = lean_grind_process_new_facts(v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; 
lean_dec_ref_known(v___x_771_, 1);
v___x_772_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_768_, v_a_770_, v_a_441_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; uint8_t v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
v___x_774_ = lean_unbox(v_a_773_);
lean_dec(v_a_773_);
if (v___x_774_ == 0)
{
lean_dec(v_a_770_);
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_del_object(v___x_511_);
v___y_519_ = v_a_439_;
v___y_520_ = v_a_441_;
v___y_521_ = v_a_442_;
v___y_522_ = v_a_443_;
v___y_523_ = v_a_444_;
v___y_524_ = v_a_445_;
v___y_525_ = v_a_446_;
v___y_526_ = v_a_447_;
v___y_527_ = v_a_448_;
v___y_528_ = v_a_449_;
v___y_529_ = v_a_450_;
goto v___jp_518_;
}
else
{
lean_object* v___x_775_; 
lean_inc(v_a_770_);
lean_inc(v_a_768_);
v___x_775_ = l_Lean_Meta_Grind_hasSameType(v_a_768_, v_a_770_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; uint8_t v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = lean_unbox(v_a_776_);
lean_dec(v_a_776_);
if (v___x_777_ == 0)
{
lean_dec(v_a_770_);
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_del_object(v___x_511_);
v___y_519_ = v_a_439_;
v___y_520_ = v_a_441_;
v___y_521_ = v_a_442_;
v___y_522_ = v_a_443_;
v___y_523_ = v_a_444_;
v___y_524_ = v_a_445_;
v___y_525_ = v_a_446_;
v___y_526_ = v_a_447_;
v___y_527_ = v_a_448_;
v___y_528_ = v_a_449_;
v___y_529_ = v_a_450_;
goto v___jp_518_;
}
else
{
lean_object* v___x_778_; 
lean_del_object(v___x_503_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
lean_inc(v_a_450_);
lean_inc_ref(v_a_449_);
lean_inc(v_a_448_);
lean_inc_ref(v_a_447_);
lean_inc(v_a_768_);
v___x_778_ = lean_infer_type(v_a_768_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_809_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_809_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_809_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_809_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_cache_783_; lean_object* v_varTypes_784_; lean_object* v_lhss_785_; lean_object* v_rhss_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_808_; 
v_cache_783_ = lean_ctor_get(v_snd_514_, 0);
v_varTypes_784_ = lean_ctor_get(v_snd_514_, 1);
v_lhss_785_ = lean_ctor_get(v_snd_514_, 2);
v_rhss_786_ = lean_ctor_get(v_snd_514_, 3);
v_isSharedCheck_808_ = !lean_is_exclusive(v_snd_514_);
if (v_isSharedCheck_808_ == 0)
{
v___x_788_ = v_snd_514_;
v_isShared_789_ = v_isSharedCheck_808_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_rhss_786_);
lean_inc(v_lhss_785_);
lean_inc(v_varTypes_784_);
lean_inc(v_cache_783_);
lean_dec(v_snd_514_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_808_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_790_ = lean_array_get_size(v_varTypes_784_);
v___x_791_ = lean_nat_add(v___x_790_, v_a_439_);
v___x_792_ = lean_array_push(v_varTypes_784_, v_a_779_);
v___x_793_ = lean_array_push(v_lhss_785_, v_a_768_);
v___x_794_ = lean_array_push(v_rhss_786_, v_a_770_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 3, v___x_794_);
lean_ctor_set(v___x_788_, 2, v___x_793_);
lean_ctor_set(v___x_788_, 1, v___x_792_);
v___x_796_ = v___x_788_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_cache_783_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___x_794_);
v___x_796_ = v_reuseFailAlloc_807_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = l_Lean_mkBVar(v___x_791_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_796_);
lean_ctor_set(v___x_516_, 0, v___x_797_);
v___x_799_ = v___x_516_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_796_);
v___x_799_ = v_reuseFailAlloc_806_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_799_);
v___x_801_ = v___x_511_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_801_);
v___x_803_ = v___x_781_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
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
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_a_770_);
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_dec(v_snd_514_);
lean_del_object(v___x_511_);
v_a_810_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_778_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_778_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_a_770_);
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_dec(v_snd_514_);
lean_del_object(v___x_511_);
lean_del_object(v___x_503_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v_a_818_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_775_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_775_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_a_770_);
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_dec(v_snd_514_);
lean_del_object(v___x_511_);
lean_del_object(v___x_503_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v_a_826_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_772_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_772_);
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
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_770_);
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_dec(v_snd_514_);
lean_del_object(v___x_511_);
lean_del_object(v___x_503_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v_a_834_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_771_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_771_);
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
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_768_);
lean_del_object(v___x_516_);
lean_dec(v_snd_514_);
lean_del_object(v___x_511_);
lean_del_object(v___x_503_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v_a_842_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_769_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_769_);
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
lean_del_object(v___x_516_);
lean_dec(v_snd_514_);
lean_del_object(v___x_511_);
lean_del_object(v___x_503_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v_a_850_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_767_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_767_);
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
lean_del_object(v___x_516_);
lean_del_object(v___x_511_);
v___y_519_ = v_a_439_;
v___y_520_ = v_a_441_;
v___y_521_ = v_a_442_;
v___y_522_ = v_a_443_;
v___y_523_ = v_a_444_;
v___y_524_ = v_a_445_;
v___y_525_ = v_a_446_;
v___y_526_ = v_a_447_;
v___y_527_ = v_a_448_;
v___y_528_ = v_a_449_;
v___y_529_ = v_a_450_;
goto v___jp_518_;
}
}
else
{
lean_del_object(v___x_516_);
lean_del_object(v___x_511_);
v___y_519_ = v_a_439_;
v___y_520_ = v_a_441_;
v___y_521_ = v_a_442_;
v___y_522_ = v_a_443_;
v___y_523_ = v_a_444_;
v___y_524_ = v_a_445_;
v___y_525_ = v_a_446_;
v___y_526_ = v_a_447_;
v___y_527_ = v_a_448_;
v___y_528_ = v_a_449_;
v___y_529_ = v_a_450_;
goto v___jp_518_;
}
}
v___jp_518_:
{
switch(lean_obj_tag(v_lhs_437_))
{
case 5:
{
if (lean_obj_tag(v_rhs_438_) == 5)
{
lean_object* v_fn_530_; lean_object* v_arg_531_; lean_object* v_fn_532_; lean_object* v_arg_533_; lean_object* v___x_534_; 
lean_del_object(v___x_503_);
v_fn_530_ = lean_ctor_get(v_lhs_437_, 0);
lean_inc_ref(v_fn_530_);
v_arg_531_ = lean_ctor_get(v_lhs_437_, 1);
lean_inc_ref(v_arg_531_);
lean_dec_ref_known(v_lhs_437_, 2);
v_fn_532_ = lean_ctor_get(v_rhs_438_, 0);
lean_inc_ref(v_fn_532_);
v_arg_533_ = lean_ctor_get(v_rhs_438_, 1);
lean_inc_ref(v_arg_533_);
lean_dec_ref_known(v_rhs_438_, 2);
v___x_534_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_fn_530_, v_fn_532_, v___y_519_, v_snd_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
if (lean_obj_tag(v_a_535_) == 0)
{
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_531_);
return v___x_534_;
}
else
{
lean_object* v_val_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v___x_534_, 1);
v_val_536_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_a_535_, 1);
v_fst_537_ = lean_ctor_get(v_val_536_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v_val_536_, 1);
lean_inc(v_snd_538_);
lean_dec(v_val_536_);
v___x_539_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_arg_531_, v_arg_533_, v___y_519_, v_snd_538_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
if (lean_obj_tag(v_a_540_) == 0)
{
lean_dec(v_fst_537_);
return v___x_539_;
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_565_; 
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_539_, 0);
lean_dec(v_unused_566_);
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_565_;
goto v_resetjp_541_;
}
else
{
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_565_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_564_; 
v_val_544_ = lean_ctor_get(v_a_540_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_564_ == 0)
{
v___x_546_ = v_a_540_;
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v_a_540_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_563_; 
v_fst_548_ = lean_ctor_get(v_val_544_, 0);
v_snd_549_ = lean_ctor_get(v_val_544_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_val_544_);
if (v_isSharedCheck_563_ == 0)
{
v___x_551_ = v_val_544_;
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snd_549_);
lean_inc(v_fst_548_);
lean_dec(v_val_544_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_Expr_app___override(v_fst_537_, v_fst_548_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_snd_549_);
v___x_555_ = v_reuseFailAlloc_562_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_555_);
v___x_557_ = v___x_546_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_557_);
v___x_559_ = v___x_542_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
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
lean_dec(v_fst_537_);
return v___x_539_;
}
}
}
else
{
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_531_);
return v___x_534_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec_ref_known(v_lhs_437_, 2);
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
v___x_567_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_567_);
v___x_569_ = v___x_503_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
case 6:
{
if (lean_obj_tag(v_rhs_438_) == 6)
{
lean_object* v_binderName_571_; lean_object* v_binderType_572_; lean_object* v_body_573_; uint8_t v_binderInfo_574_; lean_object* v_binderType_575_; lean_object* v_body_576_; lean_object* v___x_577_; 
lean_del_object(v___x_503_);
v_binderName_571_ = lean_ctor_get(v_lhs_437_, 0);
lean_inc(v_binderName_571_);
v_binderType_572_ = lean_ctor_get(v_lhs_437_, 1);
lean_inc_ref(v_binderType_572_);
v_body_573_ = lean_ctor_get(v_lhs_437_, 2);
lean_inc_ref(v_body_573_);
v_binderInfo_574_ = lean_ctor_get_uint8(v_lhs_437_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_437_, 3);
v_binderType_575_ = lean_ctor_get(v_rhs_438_, 1);
lean_inc_ref(v_binderType_575_);
v_body_576_ = lean_ctor_get(v_rhs_438_, 2);
lean_inc_ref(v_body_576_);
lean_dec_ref_known(v_rhs_438_, 3);
v___x_577_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_572_, v_binderType_575_, v___y_519_, v_snd_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
if (lean_obj_tag(v_a_578_) == 0)
{
lean_dec_ref(v_body_576_);
lean_dec_ref(v_body_573_);
lean_dec(v_binderName_571_);
return v___x_577_;
}
else
{
lean_object* v_val_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref_known(v___x_577_, 1);
v_val_579_ = lean_ctor_get(v_a_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v_a_578_, 1);
v_fst_580_ = lean_ctor_get(v_val_579_, 0);
lean_inc(v_fst_580_);
v_snd_581_ = lean_ctor_get(v_val_579_, 1);
lean_inc(v_snd_581_);
lean_dec(v_val_579_);
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v___y_519_, v___x_582_);
v___x_584_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_573_, v_body_576_, v___x_583_, v_snd_581_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
if (lean_obj_tag(v_a_585_) == 0)
{
lean_dec(v_fst_580_);
lean_dec(v_binderName_571_);
return v___x_584_;
}
else
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_610_; 
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_611_);
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_610_;
goto v_resetjp_586_;
}
else
{
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_610_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_val_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_609_; 
v_val_589_ = lean_ctor_get(v_a_585_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_a_585_);
if (v_isSharedCheck_609_ == 0)
{
v___x_591_ = v_a_585_;
v_isShared_592_ = v_isSharedCheck_609_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_val_589_);
lean_dec(v_a_585_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_609_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_608_; 
v_fst_593_ = lean_ctor_get(v_val_589_, 0);
v_snd_594_ = lean_ctor_get(v_val_589_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_val_589_);
if (v_isSharedCheck_608_ == 0)
{
v___x_596_ = v_val_589_;
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snd_594_);
lean_inc(v_fst_593_);
lean_dec(v_val_589_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_mkLambda(v_binderName_571_, v_binderInfo_574_, v_fst_580_, v_fst_593_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_snd_594_);
v___x_600_ = v_reuseFailAlloc_607_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_600_);
v___x_602_ = v___x_591_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_604_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_602_);
v___x_604_ = v___x_587_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
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
}
}
}
}
else
{
lean_dec(v_fst_580_);
lean_dec(v_binderName_571_);
return v___x_584_;
}
}
}
else
{
lean_dec_ref(v_body_576_);
lean_dec_ref(v_body_573_);
lean_dec(v_binderName_571_);
return v___x_577_;
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_614_; 
lean_dec_ref_known(v_lhs_437_, 3);
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
v___x_612_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_612_);
v___x_614_ = v___x_503_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
case 7:
{
if (lean_obj_tag(v_rhs_438_) == 7)
{
lean_object* v_binderName_616_; lean_object* v_binderType_617_; lean_object* v_body_618_; uint8_t v_binderInfo_619_; lean_object* v_binderType_620_; lean_object* v_body_621_; lean_object* v___x_622_; 
lean_del_object(v___x_503_);
v_binderName_616_ = lean_ctor_get(v_lhs_437_, 0);
lean_inc(v_binderName_616_);
v_binderType_617_ = lean_ctor_get(v_lhs_437_, 1);
lean_inc_ref(v_binderType_617_);
v_body_618_ = lean_ctor_get(v_lhs_437_, 2);
lean_inc_ref(v_body_618_);
v_binderInfo_619_ = lean_ctor_get_uint8(v_lhs_437_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_437_, 3);
v_binderType_620_ = lean_ctor_get(v_rhs_438_, 1);
lean_inc_ref(v_binderType_620_);
v_body_621_ = lean_ctor_get(v_rhs_438_, 2);
lean_inc_ref(v_body_621_);
lean_dec_ref_known(v_rhs_438_, 3);
v___x_622_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_617_, v_binderType_620_, v___y_519_, v_snd_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
if (lean_obj_tag(v_a_623_) == 0)
{
lean_dec_ref(v_body_621_);
lean_dec_ref(v_body_618_);
lean_dec(v_binderName_616_);
return v___x_622_;
}
else
{
lean_object* v_val_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref_known(v___x_622_, 1);
v_val_624_ = lean_ctor_get(v_a_623_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_a_623_, 1);
v_fst_625_ = lean_ctor_get(v_val_624_, 0);
lean_inc(v_fst_625_);
v_snd_626_ = lean_ctor_get(v_val_624_, 1);
lean_inc(v_snd_626_);
lean_dec(v_val_624_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v___y_519_, v___x_627_);
v___x_629_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_618_, v_body_621_, v___x_628_, v_snd_626_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
if (lean_obj_tag(v_a_630_) == 0)
{
lean_dec(v_fst_625_);
lean_dec(v_binderName_616_);
return v___x_629_;
}
else
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_655_; 
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v___x_629_, 0);
lean_dec(v_unused_656_);
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_655_;
goto v_resetjp_631_;
}
else
{
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_655_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_654_; 
v_val_634_ = lean_ctor_get(v_a_630_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_654_ == 0)
{
v___x_636_ = v_a_630_;
v_isShared_637_ = v_isSharedCheck_654_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_dec(v_a_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_654_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_653_; 
v_fst_638_ = lean_ctor_get(v_val_634_, 0);
v_snd_639_ = lean_ctor_get(v_val_634_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_val_634_);
if (v_isSharedCheck_653_ == 0)
{
v___x_641_ = v_val_634_;
v_isShared_642_ = v_isSharedCheck_653_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec(v_val_634_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_653_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = l_Lean_mkForall(v_binderName_616_, v_binderInfo_619_, v_fst_625_, v_fst_638_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_639_);
v___x_645_ = v_reuseFailAlloc_652_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_645_);
v___x_647_ = v___x_636_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_647_);
v___x_649_ = v___x_632_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
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
lean_dec(v_fst_625_);
lean_dec(v_binderName_616_);
return v___x_629_;
}
}
}
else
{
lean_dec_ref(v_body_621_);
lean_dec_ref(v_body_618_);
lean_dec(v_binderName_616_);
return v___x_622_;
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_dec_ref_known(v_lhs_437_, 3);
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
v___x_657_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_657_);
v___x_659_ = v___x_503_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
case 8:
{
if (lean_obj_tag(v_rhs_438_) == 8)
{
lean_object* v_declName_661_; lean_object* v_type_662_; lean_object* v_value_663_; lean_object* v_body_664_; uint8_t v_nondep_665_; lean_object* v_type_666_; lean_object* v_value_667_; lean_object* v_body_668_; lean_object* v___x_669_; 
lean_del_object(v___x_503_);
v_declName_661_ = lean_ctor_get(v_lhs_437_, 0);
lean_inc(v_declName_661_);
v_type_662_ = lean_ctor_get(v_lhs_437_, 1);
lean_inc_ref(v_type_662_);
v_value_663_ = lean_ctor_get(v_lhs_437_, 2);
lean_inc_ref(v_value_663_);
v_body_664_ = lean_ctor_get(v_lhs_437_, 3);
lean_inc_ref(v_body_664_);
v_nondep_665_ = lean_ctor_get_uint8(v_lhs_437_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_lhs_437_, 4);
v_type_666_ = lean_ctor_get(v_rhs_438_, 1);
lean_inc_ref(v_type_666_);
v_value_667_ = lean_ctor_get(v_rhs_438_, 2);
lean_inc_ref(v_value_667_);
v_body_668_ = lean_ctor_get(v_rhs_438_, 3);
lean_inc_ref(v_body_668_);
lean_dec_ref_known(v_rhs_438_, 4);
v___x_669_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_type_662_, v_type_666_, v___y_519_, v_snd_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
if (lean_obj_tag(v_a_670_) == 0)
{
lean_dec_ref(v_body_668_);
lean_dec_ref(v_value_667_);
lean_dec_ref(v_body_664_);
lean_dec_ref(v_value_663_);
lean_dec(v_declName_661_);
return v___x_669_;
}
else
{
lean_object* v_val_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_674_; 
lean_dec_ref_known(v___x_669_, 1);
v_val_671_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_a_670_, 1);
v_fst_672_ = lean_ctor_get(v_val_671_, 0);
lean_inc(v_fst_672_);
v_snd_673_ = lean_ctor_get(v_val_671_, 1);
lean_inc(v_snd_673_);
lean_dec(v_val_671_);
v___x_674_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_value_663_, v_value_667_, v___y_519_, v_snd_673_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
if (lean_obj_tag(v_a_675_) == 0)
{
lean_dec(v_fst_672_);
lean_dec_ref(v_body_668_);
lean_dec_ref(v_body_664_);
lean_dec(v_declName_661_);
return v___x_674_;
}
else
{
lean_object* v_val_676_; lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_674_, 1);
v_val_676_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v_a_675_, 1);
v_fst_677_ = lean_ctor_get(v_val_676_, 0);
lean_inc(v_fst_677_);
v_snd_678_ = lean_ctor_get(v_val_676_, 1);
lean_inc(v_snd_678_);
lean_dec(v_val_676_);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v___y_519_, v___x_679_);
v___x_681_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_664_, v_body_668_, v___x_680_, v_snd_678_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
if (lean_obj_tag(v_a_682_) == 0)
{
lean_dec(v_fst_677_);
lean_dec(v_fst_672_);
lean_dec(v_declName_661_);
return v___x_681_;
}
else
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_708_);
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_707_;
goto v_resetjp_683_;
}
else
{
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_707_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_val_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_706_; 
v_val_686_ = lean_ctor_get(v_a_682_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v_a_682_);
if (v_isSharedCheck_706_ == 0)
{
v___x_688_ = v_a_682_;
v_isShared_689_ = v_isSharedCheck_706_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_val_686_);
lean_dec(v_a_682_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_706_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_705_; 
v_fst_690_ = lean_ctor_get(v_val_686_, 0);
v_snd_691_ = lean_ctor_get(v_val_686_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_val_686_);
if (v_isSharedCheck_705_ == 0)
{
v___x_693_ = v_val_686_;
v_isShared_694_ = v_isSharedCheck_705_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_inc(v_fst_690_);
lean_dec(v_val_686_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_705_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_Expr_letE___override(v_declName_661_, v_fst_672_, v_fst_677_, v_fst_690_, v_nondep_665_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_691_);
v___x_697_ = v_reuseFailAlloc_704_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_697_);
v___x_699_ = v___x_688_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_699_);
v___x_701_ = v___x_684_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
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
lean_dec(v_fst_677_);
lean_dec(v_fst_672_);
lean_dec(v_declName_661_);
return v___x_681_;
}
}
}
else
{
lean_dec(v_fst_672_);
lean_dec_ref(v_body_668_);
lean_dec_ref(v_body_664_);
lean_dec(v_declName_661_);
return v___x_674_;
}
}
}
else
{
lean_dec_ref(v_body_668_);
lean_dec_ref(v_value_667_);
lean_dec_ref(v_body_664_);
lean_dec_ref(v_value_663_);
lean_dec(v_declName_661_);
return v___x_669_;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec_ref_known(v_lhs_437_, 4);
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
v___x_709_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_709_);
v___x_711_ = v___x_503_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
case 10:
{
if (lean_obj_tag(v_rhs_438_) == 10)
{
lean_object* v_data_713_; lean_object* v_expr_714_; lean_object* v_expr_715_; lean_object* v___x_716_; 
lean_del_object(v___x_503_);
v_data_713_ = lean_ctor_get(v_lhs_437_, 0);
lean_inc(v_data_713_);
v_expr_714_ = lean_ctor_get(v_lhs_437_, 1);
lean_inc_ref(v_expr_714_);
lean_dec_ref_known(v_lhs_437_, 2);
v_expr_715_ = lean_ctor_get(v_rhs_438_, 1);
lean_inc_ref(v_expr_715_);
lean_dec_ref_known(v_rhs_438_, 2);
v___x_716_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_expr_714_, v_expr_715_, v___y_519_, v_snd_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
if (lean_obj_tag(v_a_717_) == 0)
{
lean_dec(v_data_713_);
return v___x_716_;
}
else
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_716_, 0);
lean_dec(v_unused_743_);
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_742_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_742_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_741_; 
v_val_721_ = lean_ctor_get(v_a_717_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_717_);
if (v_isSharedCheck_741_ == 0)
{
v___x_723_ = v_a_717_;
v_isShared_724_ = v_isSharedCheck_741_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v_a_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_741_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_fst_725_; lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_740_; 
v_fst_725_ = lean_ctor_get(v_val_721_, 0);
v_snd_726_ = lean_ctor_get(v_val_721_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_val_721_);
if (v_isSharedCheck_740_ == 0)
{
v___x_728_ = v_val_721_;
v_isShared_729_ = v_isSharedCheck_740_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_inc(v_fst_725_);
lean_dec(v_val_721_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_740_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = l_Lean_Expr_mdata___override(v_data_713_, v_fst_725_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_726_);
v___x_732_ = v_reuseFailAlloc_739_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_732_);
v___x_734_ = v___x_723_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_734_);
v___x_736_ = v___x_719_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
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
}
}
}
}
else
{
lean_dec(v_data_713_);
return v___x_716_;
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec_ref_known(v_lhs_437_, 2);
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
v___x_744_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_744_);
v___x_746_ = v___x_503_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
case 11:
{
if (lean_obj_tag(v_rhs_438_) == 11)
{
lean_object* v_typeName_748_; lean_object* v_idx_749_; lean_object* v_struct_750_; lean_object* v_typeName_751_; lean_object* v_idx_752_; lean_object* v_struct_753_; uint8_t v___x_754_; 
lean_del_object(v___x_503_);
v_typeName_748_ = lean_ctor_get(v_lhs_437_, 0);
lean_inc(v_typeName_748_);
v_idx_749_ = lean_ctor_get(v_lhs_437_, 1);
lean_inc(v_idx_749_);
v_struct_750_ = lean_ctor_get(v_lhs_437_, 2);
lean_inc_ref(v_struct_750_);
lean_dec_ref_known(v_lhs_437_, 3);
v_typeName_751_ = lean_ctor_get(v_rhs_438_, 0);
lean_inc(v_typeName_751_);
v_idx_752_ = lean_ctor_get(v_rhs_438_, 1);
lean_inc(v_idx_752_);
v_struct_753_ = lean_ctor_get(v_rhs_438_, 2);
lean_inc_ref(v_struct_753_);
lean_dec_ref_known(v_rhs_438_, 3);
v___x_754_ = lean_name_eq(v_typeName_748_, v_typeName_751_);
lean_dec(v_typeName_751_);
if (v___x_754_ == 0)
{
lean_dec(v_idx_752_);
v___y_453_ = v_snd_514_;
v___y_454_ = v___y_520_;
v___y_455_ = v___y_522_;
v___y_456_ = v___y_527_;
v___y_457_ = v___y_528_;
v___y_458_ = v___y_523_;
v___y_459_ = v___y_529_;
v___y_460_ = v___y_525_;
v___y_461_ = v___y_519_;
v___y_462_ = v_typeName_748_;
v___y_463_ = v___y_524_;
v___y_464_ = v_struct_750_;
v___y_465_ = v___y_521_;
v___y_466_ = v_idx_749_;
v___y_467_ = v_struct_753_;
v___y_468_ = v___y_526_;
v___y_469_ = v___x_754_;
goto v___jp_452_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_eq(v_idx_749_, v_idx_752_);
lean_dec(v_idx_752_);
v___y_453_ = v_snd_514_;
v___y_454_ = v___y_520_;
v___y_455_ = v___y_522_;
v___y_456_ = v___y_527_;
v___y_457_ = v___y_528_;
v___y_458_ = v___y_523_;
v___y_459_ = v___y_529_;
v___y_460_ = v___y_525_;
v___y_461_ = v___y_519_;
v___y_462_ = v_typeName_748_;
v___y_463_ = v___y_524_;
v___y_464_ = v_struct_750_;
v___y_465_ = v___y_521_;
v___y_466_ = v_idx_749_;
v___y_467_ = v_struct_753_;
v___y_468_ = v___y_526_;
v___y_469_ = v___x_755_;
goto v___jp_452_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec_ref_known(v_lhs_437_, 3);
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
v___x_756_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_756_);
v___x_758_ = v___x_503_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
default: 
{
lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec(v_snd_514_);
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v___x_760_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_760_);
v___x_762_ = v___x_503_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
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
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v_rhs_438_);
lean_dec_ref(v_lhs_437_);
v_a_861_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_500_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_500_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
v___jp_452_:
{
if (v___y_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_453_);
v___x_470_ = lean_box(0);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_464_, v___y_467_, v___y_461_, v___y_453_, v___y_454_, v___y_465_, v___y_455_, v___y_458_, v___y_463_, v___y_460_, v___y_468_, v___y_456_, v___y_457_, v___y_459_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
if (lean_obj_tag(v_a_473_) == 0)
{
lean_dec(v___y_466_);
lean_dec(v___y_462_);
return v___x_472_;
}
else
{
lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_498_; 
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v___x_472_, 0);
lean_dec(v_unused_499_);
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_498_;
goto v_resetjp_474_;
}
else
{
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_498_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_val_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_497_; 
v_val_477_ = lean_ctor_get(v_a_473_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_473_);
if (v_isSharedCheck_497_ == 0)
{
v___x_479_ = v_a_473_;
v_isShared_480_ = v_isSharedCheck_497_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_val_477_);
lean_dec(v_a_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_497_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_496_; 
v_fst_481_ = lean_ctor_get(v_val_477_, 0);
v_snd_482_ = lean_ctor_get(v_val_477_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_val_477_);
if (v_isSharedCheck_496_ == 0)
{
v___x_484_ = v_val_477_;
v_isShared_485_ = v_isSharedCheck_496_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_481_);
lean_dec(v_val_477_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_496_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Lean_Expr_proj___override(v___y_462_, v___y_466_, v_fst_481_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_snd_482_);
v___x_488_ = v_reuseFailAlloc_495_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_488_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_490_);
v___x_492_ = v___x_475_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
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
lean_dec(v___y_466_);
lean_dec(v___y_462_);
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object* v_lhs_869_, lean_object* v_rhs_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
size_t v___x_884_; size_t v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_ptr_addr(v_lhs_869_);
v___x_885_ = lean_ptr_addr(v_rhs_870_);
v___x_886_ = lean_usize_dec_eq(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v_cache_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_cache_887_ = lean_ctor_get(v_a_872_, 0);
lean_inc_ref(v_rhs_870_);
lean_inc_ref(v_lhs_869_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_lhs_869_);
lean_ctor_set(v___x_888_, 1, v_rhs_870_);
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_887_, v___x_888_);
if (lean_obj_tag(v___x_889_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref_known(v___x_888_, 2);
lean_dec_ref(v_rhs_870_);
lean_dec_ref(v_lhs_869_);
v_val_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_899_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_899_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_899_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_val_890_);
lean_ctor_set(v___x_894_, 1, v_a_872_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_898_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
else
{
lean_object* v___x_900_; 
lean_dec(v___x_889_);
v___x_900_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_869_, v_rhs_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
if (lean_obj_tag(v_a_901_) == 0)
{
lean_dec_ref_known(v___x_888_, 2);
return v___x_900_;
}
else
{
lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_1002_; 
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_1003_);
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_1002_;
goto v_resetjp_902_;
}
else
{
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_1002_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_1001_; 
v_val_905_ = lean_ctor_get(v_a_901_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_a_901_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_907_ = v_a_901_;
v_isShared_908_ = v_isSharedCheck_1001_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v_a_901_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_1001_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_snd_909_; lean_object* v_fst_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_1000_; 
v_snd_909_ = lean_ctor_get(v_val_905_, 1);
v_fst_910_ = lean_ctor_get(v_val_905_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_val_905_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_912_ = v_val_905_;
v_isShared_913_ = v_isSharedCheck_1000_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_910_);
lean_dec(v_val_905_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_1000_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_cache_914_; lean_object* v_varTypes_915_; lean_object* v_lhss_916_; lean_object* v_rhss_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_999_; 
v_cache_914_ = lean_ctor_get(v_snd_909_, 0);
v_varTypes_915_ = lean_ctor_get(v_snd_909_, 1);
v_lhss_916_ = lean_ctor_get(v_snd_909_, 2);
v_rhss_917_ = lean_ctor_get(v_snd_909_, 3);
v_isSharedCheck_999_ = !lean_is_exclusive(v_snd_909_);
if (v_isSharedCheck_999_ == 0)
{
v___x_919_ = v_snd_909_;
v_isShared_920_ = v_isSharedCheck_999_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_rhss_917_);
lean_inc(v_lhss_916_);
lean_inc(v_varTypes_915_);
lean_inc(v_cache_914_);
lean_dec(v_snd_909_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_999_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___y_922_; lean_object* v___y_936_; lean_object* v_i_937_; lean_object* v___y_943_; lean_object* v___y_953_; lean_object* v_i_954_; lean_object* v___x_969_; 
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_914_, v___x_888_);
switch(lean_obj_tag(v___x_969_))
{
case 0:
{
lean_object* v_index_970_; lean_object* v_size_971_; lean_object* v___x_972_; 
v_index_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_index_970_);
lean_dec_ref_known(v___x_969_, 3);
v_size_971_ = lean_ctor_get(v_cache_914_, 0);
lean_inc(v_size_971_);
lean_inc(v_fst_910_);
v___x_972_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_914_, v_size_971_, v_index_970_, v___x_888_, v_fst_910_);
lean_dec(v_index_970_);
v___y_922_ = v___x_972_;
goto v___jp_921_;
}
case 1:
{
lean_object* v_index_973_; lean_object* v_size_974_; lean_object* v_keyArray_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_index_973_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_index_973_);
lean_dec_ref_known(v___x_969_, 1);
v_size_974_ = lean_ctor_get(v_cache_914_, 0);
v_keyArray_975_ = lean_ctor_get(v_cache_914_, 1);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_add(v_size_974_, v___x_976_);
v___x_978_ = lean_array_get_size(v_keyArray_975_);
v___x_979_ = lean_nat_dec_lt(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_dec(v___x_977_);
lean_dec(v_index_973_);
goto v___jp_959_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_980_ = lean_unsigned_to_nat(4u);
v___x_981_ = lean_nat_mul(v___x_977_, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(3u);
v___x_983_ = lean_nat_mul(v___x_978_, v___x_982_);
v___x_984_ = lean_nat_dec_le(v___x_981_, v___x_983_);
lean_dec(v___x_983_);
lean_dec(v___x_981_);
if (v___x_984_ == 0)
{
lean_dec(v___x_977_);
lean_dec(v_index_973_);
goto v___jp_959_;
}
else
{
lean_object* v___x_985_; 
lean_inc(v_fst_910_);
v___x_985_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_914_, v___x_977_, v_index_973_, v___x_888_, v_fst_910_);
lean_dec(v_index_973_);
v___y_922_ = v___x_985_;
goto v___jp_921_;
}
}
}
default: 
{
lean_object* v_size_986_; lean_object* v_keyArray_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_size_986_ = lean_ctor_get(v_cache_914_, 0);
v_keyArray_987_ = lean_ctor_get(v_cache_914_, 1);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_nat_add(v_size_986_, v___x_988_);
v___x_990_ = lean_array_get_size(v_keyArray_987_);
v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec(v___x_989_);
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(v_cache_914_);
lean_dec_ref(v_cache_914_);
v___y_943_ = v___x_992_;
goto v___jp_942_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_993_ = lean_unsigned_to_nat(4u);
v___x_994_ = lean_nat_mul(v___x_989_, v___x_993_);
lean_dec(v___x_989_);
v___x_995_ = lean_unsigned_to_nat(3u);
v___x_996_ = lean_nat_mul(v___x_990_, v___x_995_);
v___x_997_ = lean_nat_dec_le(v___x_994_, v___x_996_);
lean_dec(v___x_996_);
lean_dec(v___x_994_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(v_cache_914_);
lean_dec_ref(v_cache_914_);
v___y_943_ = v___x_998_;
goto v___jp_942_;
}
else
{
v___y_943_ = v_cache_914_;
goto v___jp_942_;
}
}
}
}
v___jp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___y_922_);
v___x_924_ = v___x_919_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___y_922_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_varTypes_915_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_lhss_916_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_rhss_917_);
v___x_924_ = v_reuseFailAlloc_934_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_924_);
v___x_926_ = v___x_912_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_933_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_926_);
v___x_928_ = v___x_907_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_928_);
v___x_930_ = v___x_903_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
v___jp_935_:
{
lean_object* v_size_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_size_938_ = lean_ctor_get(v___y_936_, 0);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_size_938_, v___x_939_);
lean_inc(v_fst_910_);
v___x_941_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_936_, v___x_940_, v_i_937_, v___x_888_, v_fst_910_);
lean_dec(v_i_937_);
v___y_922_ = v___x_941_;
goto v___jp_921_;
}
v___jp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v___y_943_, v___x_888_);
switch(lean_obj_tag(v___x_944_))
{
case 0:
{
lean_object* v_index_945_; lean_object* v_size_946_; lean_object* v___x_947_; 
v_index_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_index_945_);
lean_dec_ref_known(v___x_944_, 3);
v_size_946_ = lean_ctor_get(v___y_943_, 0);
lean_inc(v_size_946_);
lean_inc(v_fst_910_);
v___x_947_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_943_, v_size_946_, v_index_945_, v___x_888_, v_fst_910_);
lean_dec(v_index_945_);
v___y_922_ = v___x_947_;
goto v___jp_921_;
}
case 1:
{
lean_object* v_index_948_; 
v_index_948_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_index_948_);
lean_dec_ref_known(v___x_944_, 1);
v___y_936_ = v___y_943_;
v_i_937_ = v_index_948_;
goto v___jp_935_;
}
default: 
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_943_, v___x_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_index_951_; 
v_index_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_index_951_);
lean_dec_ref_known(v___x_950_, 1);
v___y_936_ = v___y_943_;
v_i_937_ = v_index_951_;
goto v___jp_935_;
}
else
{
lean_dec_ref_known(v___x_888_, 2);
v___y_922_ = v___y_943_;
goto v___jp_921_;
}
}
}
}
v___jp_952_:
{
lean_object* v_size_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_size_955_ = lean_ctor_get(v___y_953_, 0);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_size_955_, v___x_956_);
lean_inc(v_fst_910_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_953_, v___x_957_, v_i_954_, v___x_888_, v_fst_910_);
lean_dec(v_i_954_);
v___y_922_ = v___x_958_;
goto v___jp_921_;
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(v_cache_914_);
lean_dec_ref(v_cache_914_);
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v___x_960_, v___x_888_);
switch(lean_obj_tag(v___x_961_))
{
case 0:
{
lean_object* v_index_962_; lean_object* v_size_963_; lean_object* v___x_964_; 
v_index_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_index_962_);
lean_dec_ref_known(v___x_961_, 3);
v_size_963_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_size_963_);
lean_inc(v_fst_910_);
v___x_964_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_960_, v_size_963_, v_index_962_, v___x_888_, v_fst_910_);
lean_dec(v_index_962_);
v___y_922_ = v___x_964_;
goto v___jp_921_;
}
case 1:
{
lean_object* v_index_965_; 
v_index_965_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_index_965_);
lean_dec_ref_known(v___x_961_, 1);
v___y_953_ = v___x_960_;
v_i_954_ = v_index_965_;
goto v___jp_952_;
}
default: 
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_960_, v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_index_968_; 
v_index_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_index_968_);
lean_dec_ref_known(v___x_967_, 1);
v___y_953_ = v___x_960_;
v_i_954_ = v_index_968_;
goto v___jp_952_;
}
else
{
lean_dec_ref_known(v___x_888_, 2);
v___y_922_ = v___x_960_;
goto v___jp_921_;
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
lean_dec_ref_known(v___x_888_, 2);
return v___x_900_;
}
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_rhs_870_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_lhs_869_);
lean_ctor_set(v___x_1004_, 1, v_a_872_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object* v_lhs_1007_, lean_object* v_rhs_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_1007_, v_rhs_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec(v_a_1009_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object* v_lhs_1023_, lean_object* v_rhs_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_1023_, v_rhs_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec(v_a_1025_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(lean_object* v_00_u03b2_1039_, lean_object* v_m_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_1040_, v_a_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(lean_object* v_00_u03b2_1043_, lean_object* v_m_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(v_00_u03b2_1043_, v_m_1044_, v_a_1045_);
lean_dec_ref(v_a_1045_);
lean_dec_ref(v_m_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object* v_00_u03b2_1047_, lean_object* v_m_1048_, lean_object* v_query_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_1048_, v_query_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_m_1052_, lean_object* v_query_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(v_00_u03b2_1051_, v_m_1052_, v_query_1053_);
lean_dec_ref(v_query_1053_);
lean_dec_ref(v_m_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3(lean_object* v_00_u03b2_1055_, lean_object* v_m_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___redArg(v_m_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3___boxed(lean_object* v_00_u03b2_1058_, lean_object* v_m_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3(v_00_u03b2_1058_, v_m_1059_);
lean_dec_ref(v_m_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(lean_object* v_00_u03b2_1061_, lean_object* v_m_1062_, lean_object* v_query_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_m_1062_, v_query_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1065_, lean_object* v_m_1066_, lean_object* v_query_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(v_00_u03b2_1065_, v_m_1066_, v_query_1067_);
lean_dec_ref(v_query_1067_);
lean_dec_ref(v_m_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object* v_00_u03b2_1069_, lean_object* v_m_1070_, lean_object* v_query_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_m_1070_, v_query_1071_, v_x_1072_, v_x_1073_, v_x_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1077_, lean_object* v_m_1078_, lean_object* v_query_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_1077_, v_m_1078_, v_query_1079_, v_x_1080_, v_x_1081_, v_x_1082_, v_x_1083_);
lean_dec_ref(v_query_1079_);
lean_dec_ref(v_m_1078_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5(lean_object* v_00_u03b2_1085_, lean_object* v_init_1086_, lean_object* v_b_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___redArg(v_init_1086_, v_b_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1089_, lean_object* v_init_1090_, lean_object* v_b_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5(v_00_u03b2_1089_, v_init_1090_, v_b_1091_);
lean_dec_ref(v_b_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1093_, lean_object* v_b_1094_, lean_object* v_acc_1095_, lean_object* v_i_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___redArg(v_b_1094_, v_acc_1095_, v_i_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1098_, lean_object* v_b_1099_, lean_object* v_acc_1100_, lean_object* v_i_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__3_spec__5_spec__6(v_00_u03b2_1098_, v_b_1099_, v_acc_1100_, v_i_1101_);
lean_dec_ref(v_b_1099_);
return v_res_1102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0(void){
_start:
{
lean_object* v_cellCount_1103_; lean_object* v___x_1104_; 
v_cellCount_1103_ = lean_unsigned_to_nat(16u);
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1(void){
_start:
{
lean_object* v_cellCount_1105_; lean_object* v___x_1106_; 
v_cellCount_1105_ = lean_unsigned_to_nat(16u);
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v___x_1108_);
lean_ctor_set(v___x_1110_, 2, v___x_1107_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3));
v___x_1114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2);
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1113_);
lean_ctor_set(v___x_1115_, 2, v___x_1113_);
lean_ctor_set(v___x_1115_, 3, v___x_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object* v_lhs_1123_, lean_object* v_rhs_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_Sym_shareCommon(v_lhs_1123_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = l_Lean_Meta_Sym_shareCommon(v_rhs_1124_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4);
v___x_1142_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_1137_, v_a_1139_, v___x_1140_, v___x_1141_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1212_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1212_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1212_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
if (lean_obj_tag(v_a_1143_) == 1)
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1207_; 
v_val_1147_ = lean_ctor_get(v_a_1143_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1143_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1149_ = v_a_1143_;
v_isShared_1150_ = v_isSharedCheck_1207_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v_a_1143_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1207_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_snd_1151_; lean_object* v_fst_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1206_; 
v_snd_1151_ = lean_ctor_get(v_val_1147_, 1);
v_fst_1152_ = lean_ctor_get(v_val_1147_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_val_1147_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1154_ = v_val_1147_;
v_isShared_1155_ = v_isSharedCheck_1206_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1152_);
lean_dec(v_val_1147_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1206_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_varTypes_1156_; lean_object* v_lhss_1157_; lean_object* v_rhss_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_varTypes_1156_ = lean_ctor_get(v_snd_1151_, 1);
lean_inc_ref(v_varTypes_1156_);
v_lhss_1157_ = lean_ctor_get(v_snd_1151_, 2);
lean_inc_ref(v_lhss_1157_);
v_rhss_1158_ = lean_ctor_get(v_snd_1151_, 3);
lean_inc_ref(v_rhss_1158_);
lean_dec(v_snd_1151_);
v___x_1159_ = lean_array_get_size(v_lhss_1157_);
v___x_1160_ = lean_nat_dec_eq(v___x_1159_, v___x_1140_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_1145_);
v___x_1161_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_1156_, v_fst_1152_);
lean_dec_ref(v_varTypes_1156_);
lean_inc(v_a_1134_);
lean_inc_ref(v_a_1133_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc_ref(v___x_1161_);
v___x_1162_ = lean_infer_type(v___x_1161_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_n(v_a_1163_, 2);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_Meta_getLevel(v_a_1163_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1185_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1185_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1185_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__8));
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1165_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_Expr_const___override(v___x_1169_, v___x_1171_);
v___x_1173_ = l_Lean_mkAppB(v___x_1172_, v_a_1163_, v___x_1161_);
lean_inc_ref(v___x_1173_);
v___x_1174_ = l_Lean_mkAppN(v___x_1173_, v_lhss_1157_);
lean_dec_ref(v_lhss_1157_);
v___x_1175_ = l_Lean_mkAppN(v___x_1173_, v_rhss_1158_);
lean_dec_ref(v_rhss_1158_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1175_);
lean_ctor_set(v___x_1154_, 0, v___x_1174_);
v___x_1177_ = v___x_1154_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1177_);
v___x_1179_ = v___x_1149_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1179_);
v___x_1181_ = v___x_1167_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_a_1163_);
lean_dec_ref(v___x_1161_);
lean_dec_ref(v_rhss_1158_);
lean_dec_ref(v_lhss_1157_);
lean_del_object(v___x_1154_);
lean_del_object(v___x_1149_);
v_a_1186_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1164_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1164_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v___x_1161_);
lean_dec_ref(v_rhss_1158_);
lean_dec_ref(v_lhss_1157_);
lean_del_object(v___x_1154_);
lean_del_object(v___x_1149_);
v_a_1194_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1162_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1162_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec_ref(v_rhss_1158_);
lean_dec_ref(v_lhss_1157_);
lean_dec_ref(v_varTypes_1156_);
lean_del_object(v___x_1154_);
lean_dec(v_fst_1152_);
lean_del_object(v___x_1149_);
v___x_1202_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1202_);
v___x_1204_ = v___x_1145_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_dec(v_a_1143_);
v___x_1208_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1208_);
v___x_1210_ = v___x_1145_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_a_1213_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1142_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1142_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_a_1137_);
v_a_1221_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1138_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1138_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v_rhs_1124_);
v_a_1229_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1136_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1136_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object* v_lhs_1237_, lean_object* v_rhs_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_1237_, v_rhs_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec(v_a_1239_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(lean_object* v_msgData_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_env_1258_; lean_object* v___x_1259_; lean_object* v_mctx_1260_; lean_object* v_lctx_1261_; lean_object* v_options_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1257_ = lean_st_ref_get(v___y_1255_);
v_env_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_env_1258_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_st_ref_get(v___y_1253_);
v_mctx_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_mctx_1260_);
lean_dec(v___x_1259_);
v_lctx_1261_ = lean_ctor_get(v___y_1252_, 2);
v_options_1262_ = lean_ctor_get(v___y_1254_, 2);
lean_inc_ref(v_options_1262_);
lean_inc_ref(v_lctx_1261_);
v___x_1263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1263_, 0, v_env_1258_);
lean_ctor_set(v___x_1263_, 1, v_mctx_1260_);
lean_ctor_set(v___x_1263_, 2, v_lctx_1261_);
lean_ctor_set(v___x_1263_, 3, v_options_1262_);
v___x_1264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_msgData_1251_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(lean_object* v_msgData_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1272_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1273_; double v___x_1274_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_float_of_nat(v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object* v_cls_1278_, lean_object* v_msg_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_ref_1285_; lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1331_; 
v_ref_1285_ = lean_ctor_get(v___y_1282_, 5);
v___x_1286_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1331_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1331_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v_traceState_1292_; lean_object* v_env_1293_; lean_object* v_nextMacroScope_1294_; lean_object* v_ngen_1295_; lean_object* v_auxDeclNGen_1296_; lean_object* v_cache_1297_; lean_object* v_messages_1298_; lean_object* v_infoState_1299_; lean_object* v_snapshotTasks_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1330_; 
v___x_1291_ = lean_st_ref_take(v___y_1283_);
v_traceState_1292_ = lean_ctor_get(v___x_1291_, 4);
v_env_1293_ = lean_ctor_get(v___x_1291_, 0);
v_nextMacroScope_1294_ = lean_ctor_get(v___x_1291_, 1);
v_ngen_1295_ = lean_ctor_get(v___x_1291_, 2);
v_auxDeclNGen_1296_ = lean_ctor_get(v___x_1291_, 3);
v_cache_1297_ = lean_ctor_get(v___x_1291_, 5);
v_messages_1298_ = lean_ctor_get(v___x_1291_, 6);
v_infoState_1299_ = lean_ctor_get(v___x_1291_, 7);
v_snapshotTasks_1300_ = lean_ctor_get(v___x_1291_, 8);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1302_ = v___x_1291_;
v_isShared_1303_ = v_isSharedCheck_1330_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snapshotTasks_1300_);
lean_inc(v_infoState_1299_);
lean_inc(v_messages_1298_);
lean_inc(v_cache_1297_);
lean_inc(v_traceState_1292_);
lean_inc(v_auxDeclNGen_1296_);
lean_inc(v_ngen_1295_);
lean_inc(v_nextMacroScope_1294_);
lean_inc(v_env_1293_);
lean_dec(v___x_1291_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1330_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
uint64_t v_tid_1304_; lean_object* v_traces_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1329_; 
v_tid_1304_ = lean_ctor_get_uint64(v_traceState_1292_, sizeof(void*)*1);
v_traces_1305_ = lean_ctor_get(v_traceState_1292_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_traceState_1292_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1307_ = v_traceState_1292_;
v_isShared_1308_ = v_isSharedCheck_1329_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_traces_1305_);
lean_dec(v_traceState_1292_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1329_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; double v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
v___x_1311_ = 0;
v___x_1312_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1));
v___x_1313_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1313_, 0, v_cls_1278_);
lean_ctor_set(v___x_1313_, 1, v___x_1309_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
lean_ctor_set_float(v___x_1313_, sizeof(void*)*3, v___x_1310_);
lean_ctor_set_float(v___x_1313_, sizeof(void*)*3 + 8, v___x_1310_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*3 + 16, v___x_1311_);
v___x_1314_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2));
v___x_1315_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v_a_1287_);
lean_ctor_set(v___x_1315_, 2, v___x_1314_);
lean_inc(v_ref_1285_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_ref_1285_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_PersistentArray_push___redArg(v_traces_1305_, v___x_1316_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1317_);
v___x_1319_ = v___x_1307_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1317_);
lean_ctor_set_uint64(v_reuseFailAlloc_1328_, sizeof(void*)*1, v_tid_1304_);
v___x_1319_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v___x_1319_);
v___x_1321_ = v___x_1302_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_env_1293_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_nextMacroScope_1294_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_ngen_1295_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_auxDeclNGen_1296_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_cache_1297_);
lean_ctor_set(v_reuseFailAlloc_1327_, 6, v_messages_1298_);
lean_ctor_set(v_reuseFailAlloc_1327_, 7, v_infoState_1299_);
lean_ctor_set(v_reuseFailAlloc_1327_, 8, v_snapshotTasks_1300_);
v___x_1321_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1322_ = lean_st_ref_put(v___y_1283_, v___x_1321_);
v___x_1323_ = lean_box(0);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1323_);
v___x_1325_ = v___x_1289_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object* v_cls_1332_, lean_object* v_msg_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1332_, v_msg_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5));
v___x_1352_ = l_Lean_Name_append(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object* v_lhs_u2080_1362_, lean_object* v_rhs_u2080_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_1362_, v_rhs_u2080_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1500_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1500_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1500_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
if (lean_obj_tag(v_a_1376_) == 1)
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1495_; 
lean_del_object(v___x_1378_);
v_val_1380_ = lean_ctor_get(v_a_1376_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_a_1376_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1382_ = v_a_1376_;
v_isShared_1383_ = v_isSharedCheck_1495_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v_a_1376_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1495_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1494_; 
v_fst_1384_ = lean_ctor_get(v_val_1380_, 0);
v_snd_1385_ = lean_ctor_get(v_val_1380_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_val_1380_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1387_ = v_val_1380_;
v_isShared_1388_ = v_isSharedCheck_1494_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1385_);
lean_inc(v_fst_1384_);
lean_dec(v_val_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1494_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v_options_1468_; uint8_t v_hasTrace_1469_; 
v_options_1468_ = lean_ctor_get(v_a_1372_, 2);
v_hasTrace_1469_ = lean_ctor_get_uint8(v_options_1468_, sizeof(void*)*1);
if (v_hasTrace_1469_ == 0)
{
lean_del_object(v___x_1387_);
v___y_1390_ = v_a_1364_;
v___y_1391_ = v_a_1365_;
v___y_1392_ = v_a_1366_;
v___y_1393_ = v_a_1367_;
v___y_1394_ = v_a_1368_;
v___y_1395_ = v_a_1369_;
v___y_1396_ = v_a_1370_;
v___y_1397_ = v_a_1371_;
v___y_1398_ = v_a_1372_;
v___y_1399_ = v_a_1373_;
goto v___jp_1389_;
}
else
{
lean_object* v_inheritedTraceOptions_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_inheritedTraceOptions_1470_ = lean_ctor_get(v_a_1372_, 13);
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1473_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1470_, v_options_1468_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_del_object(v___x_1387_);
v___y_1390_ = v_a_1364_;
v___y_1391_ = v_a_1365_;
v___y_1392_ = v_a_1366_;
v___y_1393_ = v_a_1367_;
v___y_1394_ = v_a_1368_;
v___y_1395_ = v_a_1369_;
v___y_1396_ = v_a_1370_;
v___y_1397_ = v_a_1371_;
v___y_1398_ = v_a_1372_;
v___y_1399_ = v_a_1373_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
lean_inc(v_fst_1384_);
v___x_1475_ = l_Lean_MessageData_ofExpr(v_fst_1384_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 7);
lean_ctor_set(v___x_1387_, 1, v___x_1475_);
lean_ctor_set(v___x_1387_, 0, v___x_1474_);
v___x_1477_ = v___x_1387_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_inc(v_snd_1385_);
v___x_1480_ = l_Lean_MessageData_ofExpr(v_snd_1385_);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_1471_, v___x_1483_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref_known(v___x_1484_, 1);
v___y_1390_ = v_a_1364_;
v___y_1391_ = v_a_1365_;
v___y_1392_ = v_a_1366_;
v___y_1393_ = v_a_1367_;
v___y_1394_ = v_a_1368_;
v___y_1395_ = v_a_1369_;
v___y_1396_ = v_a_1370_;
v___y_1397_ = v_a_1371_;
v___y_1398_ = v_a_1372_;
v___y_1399_ = v_a_1373_;
goto v___jp_1389_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
v___jp_1389_:
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_1384_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_1385_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___y_1390_);
v___x_1404_ = lean_grind_process_new_facts(v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1405_; 
lean_dec_ref_known(v___x_1404_, 1);
v___x_1405_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1401_, v_a_1403_, v___y_1390_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1435_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1435_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1435_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_unbox(v_a_1406_);
lean_dec(v_a_1406_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec(v_a_1403_);
lean_dec(v_a_1401_);
lean_del_object(v___x_1382_);
v___x_1411_ = lean_box(0);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
lean_object* v___x_1415_; 
lean_del_object(v___x_1408_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___y_1390_);
v___x_1415_ = lean_grind_mk_eq_proof(v_a_1401_, v_a_1403_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v_a_1416_);
v___x_1421_ = v___x_1382_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_del_object(v___x_1382_);
v_a_1427_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1415_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1415_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_a_1403_);
lean_dec(v_a_1401_);
lean_del_object(v___x_1382_);
v_a_1436_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1405_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1405_);
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
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_a_1403_);
lean_dec(v_a_1401_);
lean_del_object(v___x_1382_);
v_a_1444_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1404_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1404_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1401_);
lean_del_object(v___x_1382_);
v_a_1452_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1402_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1402_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_snd_1385_);
lean_del_object(v___x_1382_);
v_a_1460_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1400_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1400_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
lean_dec(v_a_1376_);
v___x_1496_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1496_);
v___x_1498_ = v___x_1378_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_a_1501_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1375_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1375_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object* v_lhs_u2080_1509_, lean_object* v_rhs_u2080_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_lhs_u2080_1509_, v_rhs_u2080_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec(v_a_1511_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object* v_cls_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1523_, v_msg_1524_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object* v_cls_1537_, lean_object* v_msg_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_1537_, v_msg_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1539_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object* v_lhs_1551_, lean_object* v_rhs_1552_, uint8_t v_abstract_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1551_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc(v___y_1554_);
v___x_1569_ = lean_grind_process_new_facts(v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_dec_ref_known(v___x_1569_, 1);
v___x_1570_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1566_, v_a_1568_, v___y_1554_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1599_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1599_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1599_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_unbox(v_a_1571_);
lean_dec(v_a_1571_);
if (v___x_1575_ == 0)
{
if (v_abstract_1553_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec(v_a_1568_);
lean_dec(v_a_1566_);
v___x_1576_ = lean_box(0);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
else
{
lean_object* v___x_1580_; 
lean_del_object(v___x_1573_);
v___x_1580_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_a_1566_, v_a_1568_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1580_;
}
}
else
{
lean_object* v___x_1581_; 
lean_del_object(v___x_1573_);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc(v___y_1554_);
v___x_1581_ = lean_grind_mk_eq_proof(v_a_1566_, v_a_1568_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_a_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_a_1591_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1581_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1581_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1568_);
lean_dec(v_a_1566_);
v_a_1600_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1570_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1570_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1568_);
lean_dec(v_a_1566_);
v_a_1608_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1569_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1569_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1566_);
v_a_1616_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1567_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1567_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_rhs_1552_);
v_a_1624_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1565_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1565_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object* v_lhs_1632_, lean_object* v_rhs_1633_, lean_object* v_abstract_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_abstract_boxed_1646_; lean_object* v_res_1647_; 
v_abstract_boxed_1646_ = lean_unbox(v_abstract_1634_);
v_res_1647_ = l_Lean_Meta_Grind_proveEq_x3f___lam__0(v_lhs_1632_, v_rhs_1633_, v_abstract_boxed_1646_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec(v___y_1635_);
return v_res_1647_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Grind_proveEq_x3f___closed__0));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object* v_lhs_1651_, lean_object* v_rhs_1652_, uint8_t v_abstract_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_options_1665_; lean_object* v_inheritedTraceOptions_1666_; uint8_t v_hasTrace_1667_; lean_object* v___x_1668_; lean_object* v___f_1669_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; 
v_options_1665_ = lean_ctor_get(v_a_1662_, 2);
v_inheritedTraceOptions_1666_ = lean_ctor_get(v_a_1662_, 13);
v_hasTrace_1667_ = lean_ctor_get_uint8(v_options_1665_, sizeof(void*)*1);
v___x_1668_ = lean_box(v_abstract_1653_);
lean_inc_ref(v_rhs_1652_);
lean_inc_ref(v_lhs_1651_);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed), 14, 3);
lean_closure_set(v___f_1669_, 0, v_lhs_1651_);
lean_closure_set(v___f_1669_, 1, v_rhs_1652_);
lean_closure_set(v___f_1669_, 2, v___x_1668_);
if (v_hasTrace_1667_ == 0)
{
v___y_1733_ = v_a_1654_;
v___y_1734_ = v_a_1655_;
v___y_1735_ = v_a_1656_;
v___y_1736_ = v_a_1657_;
v___y_1737_ = v_a_1658_;
v___y_1738_ = v_a_1659_;
v___y_1739_ = v_a_1660_;
v___y_1740_ = v_a_1661_;
v___y_1741_ = v_a_1662_;
v___y_1742_ = v_a_1663_;
goto v___jp_1732_;
}
else
{
lean_object* v_cls_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_cls_1766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1666_, v_options_1665_, v___x_1767_);
if (v___x_1768_ == 0)
{
v___y_1733_ = v_a_1654_;
v___y_1734_ = v_a_1655_;
v___y_1735_ = v_a_1656_;
v___y_1736_ = v_a_1657_;
v___y_1737_ = v_a_1658_;
v___y_1738_ = v_a_1659_;
v___y_1739_ = v_a_1660_;
v___y_1740_ = v_a_1661_;
v___y_1741_ = v_a_1662_;
v___y_1742_ = v_a_1663_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1769_ = lean_obj_once(&l_Lean_Meta_Grind_proveEq_x3f___closed__1, &l_Lean_Meta_Grind_proveEq_x3f___closed__1_once, _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1);
lean_inc_ref(v_lhs_1651_);
v___x_1770_ = l_Lean_MessageData_ofExpr(v_lhs_1651_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
lean_inc_ref(v_rhs_1652_);
v___x_1774_ = l_Lean_MessageData_ofExpr(v_rhs_1652_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1766_, v___x_1777_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec_ref_known(v___x_1778_, 1);
v___y_1733_ = v_a_1654_;
v___y_1734_ = v_a_1655_;
v___y_1735_ = v_a_1656_;
v___y_1736_ = v_a_1657_;
v___y_1737_ = v_a_1658_;
v___y_1738_ = v_a_1659_;
v___y_1739_ = v_a_1660_;
v___y_1740_ = v_a_1661_;
v___y_1741_ = v_a_1662_;
v___y_1742_ = v_a_1663_;
goto v___jp_1732_;
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
v___jp_1670_:
{
if (lean_obj_tag(v___y_1681_) == 0)
{
lean_object* v_a_1682_; uint8_t v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___y_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___y_1681_, 1);
v___x_1683_ = lean_unbox(v_a_1682_);
lean_dec(v_a_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v___x_1684_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1669_, v___y_1680_, v___y_1676_, v___y_1675_, v___y_1677_, v___y_1673_, v___y_1674_, v___y_1671_, v___y_1672_, v___y_1679_, v___y_1678_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; 
lean_dec_ref(v___f_1669_);
v___x_1685_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1651_, v_rhs_1652_, v___y_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1715_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1715_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1715_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_unbox(v_a_1686_);
lean_dec(v_a_1686_);
if (v___x_1690_ == 0)
{
if (v_abstract_1653_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v___x_1691_ = lean_box(0);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_del_object(v___x_1688_);
v___x_1695_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 13, 2);
lean_closure_set(v___x_1695_, 0, v_lhs_1651_);
lean_closure_set(v___x_1695_, 1, v_rhs_1652_);
v___x_1696_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___x_1695_, v___y_1680_, v___y_1676_, v___y_1675_, v___y_1677_, v___y_1673_, v___y_1674_, v___y_1671_, v___y_1672_, v___y_1679_, v___y_1678_);
return v___x_1696_;
}
}
else
{
lean_object* v___x_1697_; 
lean_del_object(v___x_1688_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1676_);
lean_inc(v___y_1680_);
v___x_1697_ = lean_grind_mk_eq_proof(v_lhs_1651_, v_rhs_1652_, v___y_1680_, v___y_1676_, v___y_1675_, v___y_1677_, v___y_1673_, v___y_1674_, v___y_1671_, v___y_1672_, v___y_1679_, v___y_1678_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_a_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1697_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v_a_1716_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1685_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1685_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v_a_1724_ = lean_ctor_get(v___y_1681_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___y_1681_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___y_1681_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___y_1681_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
v___jp_1732_:
{
lean_object* v___x_1743_; 
lean_inc_ref(v_rhs_1652_);
lean_inc_ref(v_lhs_1651_);
v___x_1743_ = l_Lean_Meta_Grind_hasSameType(v_lhs_1651_, v_rhs_1652_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1757_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1757_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1757_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_unbox(v_a_1744_);
lean_dec(v_a_1744_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v___x_1749_ = lean_box(0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1749_);
v___x_1751_ = v___x_1746_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
else
{
lean_object* v___x_1753_; 
lean_del_object(v___x_1746_);
v___x_1753_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1651_, v___y_1733_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; uint8_t v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
v___x_1755_ = lean_unbox(v_a_1754_);
lean_dec(v_a_1754_);
if (v___x_1755_ == 0)
{
v___y_1671_ = v___y_1739_;
v___y_1672_ = v___y_1740_;
v___y_1673_ = v___y_1737_;
v___y_1674_ = v___y_1738_;
v___y_1675_ = v___y_1735_;
v___y_1676_ = v___y_1734_;
v___y_1677_ = v___y_1736_;
v___y_1678_ = v___y_1742_;
v___y_1679_ = v___y_1741_;
v___y_1680_ = v___y_1733_;
v___y_1681_ = v___x_1753_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1756_; 
lean_dec_ref_known(v___x_1753_, 1);
v___x_1756_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1652_, v___y_1733_);
v___y_1671_ = v___y_1739_;
v___y_1672_ = v___y_1740_;
v___y_1673_ = v___y_1737_;
v___y_1674_ = v___y_1738_;
v___y_1675_ = v___y_1735_;
v___y_1676_ = v___y_1734_;
v___y_1677_ = v___y_1736_;
v___y_1678_ = v___y_1742_;
v___y_1679_ = v___y_1741_;
v___y_1680_ = v___y_1733_;
v___y_1681_ = v___x_1756_;
goto v___jp_1670_;
}
}
else
{
v___y_1671_ = v___y_1739_;
v___y_1672_ = v___y_1740_;
v___y_1673_ = v___y_1737_;
v___y_1674_ = v___y_1738_;
v___y_1675_ = v___y_1735_;
v___y_1676_ = v___y_1734_;
v___y_1677_ = v___y_1736_;
v___y_1678_ = v___y_1742_;
v___y_1679_ = v___y_1741_;
v___y_1680_ = v___y_1733_;
v___y_1681_ = v___x_1753_;
goto v___jp_1670_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_rhs_1652_);
lean_dec_ref(v_lhs_1651_);
v_a_1758_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1743_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1743_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object* v_lhs_1787_, lean_object* v_rhs_1788_, lean_object* v_abstract_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
uint8_t v_abstract_boxed_1801_; lean_object* v_res_1802_; 
v_abstract_boxed_1801_ = lean_unbox(v_abstract_1789_);
v_res_1802_ = l_Lean_Meta_Grind_proveEq_x3f(v_lhs_1787_, v_rhs_1788_, v_abstract_boxed_1801_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec(v_a_1790_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object* v_lhs_1803_, lean_object* v_rhs_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1803_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1818_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc(v___y_1805_);
v___x_1820_ = lean_grind_process_new_facts(v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1821_; 
lean_dec_ref_known(v___x_1820_, 1);
v___x_1821_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1817_, v_a_1819_, v___y_1805_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1849_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1849_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1849_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_unbox(v_a_1822_);
lean_dec(v_a_1822_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec(v_a_1819_);
lean_dec(v_a_1817_);
v___x_1827_ = lean_box(0);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v___x_1831_; 
lean_del_object(v___x_1824_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc(v___y_1805_);
v___x_1831_ = lean_grind_mk_heq_proof(v_a_1817_, v_a_1819_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1832_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1831_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1831_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_a_1819_);
lean_dec(v_a_1817_);
v_a_1850_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1821_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1821_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1819_);
lean_dec(v_a_1817_);
v_a_1858_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1820_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1820_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1817_);
v_a_1866_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1818_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1818_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_rhs_1804_);
v_a_1874_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1816_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1816_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object* v_lhs_1882_, lean_object* v_rhs_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(v_lhs_1882_, v_rhs_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object* v_lhs_1896_, lean_object* v_rhs_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___f_1909_; lean_object* v___y_1911_; lean_object* v___x_1960_; 
lean_inc_ref(v_rhs_1897_);
lean_inc_ref(v_lhs_1896_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1909_, 0, v_lhs_1896_);
lean_closure_set(v___f_1909_, 1, v_rhs_1897_);
v___x_1960_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1896_, v_a_1898_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; uint8_t v___x_1962_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
v___x_1962_ = lean_unbox(v_a_1961_);
lean_dec(v_a_1961_);
if (v___x_1962_ == 0)
{
v___y_1911_ = v___x_1960_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1963_; 
lean_dec_ref_known(v___x_1960_, 1);
v___x_1963_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1897_, v_a_1898_);
v___y_1911_ = v___x_1963_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1960_;
goto v___jp_1910_;
}
v___jp_1910_:
{
if (lean_obj_tag(v___y_1911_) == 0)
{
lean_object* v_a_1912_; uint8_t v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___y_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___y_1911_, 1);
v___x_1913_ = lean_unbox(v_a_1912_);
lean_dec(v_a_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref(v_rhs_1897_);
lean_dec_ref(v_lhs_1896_);
v___x_1914_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1909_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; 
lean_dec_ref(v___f_1909_);
v___x_1915_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1896_, v_rhs_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1943_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1943_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1943_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_dec_ref(v_rhs_1897_);
lean_dec_ref(v_lhs_1896_);
v___x_1921_ = lean_box(0);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1921_);
v___x_1923_ = v___x_1918_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
lean_object* v___x_1925_; 
lean_del_object(v___x_1918_);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc(v_a_1898_);
v___x_1925_ = lean_grind_mk_heq_proof(v_lhs_1896_, v_rhs_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1934_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1934_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1934_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1926_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
v_a_1935_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1925_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1925_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_rhs_1897_);
lean_dec_ref(v_lhs_1896_);
v_a_1944_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1915_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1915_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___f_1909_);
lean_dec_ref(v_rhs_1897_);
lean_dec_ref(v_lhs_1896_);
v_a_1952_ = lean_ctor_get(v___y_1911_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1911_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___y_1911_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___y_1911_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object* v_lhs_1964_, lean_object* v_rhs_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Meta_Grind_proveHEq_x3f(v_lhs_1964_, v_rhs_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec(v_a_1966_);
return v_res_1977_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
