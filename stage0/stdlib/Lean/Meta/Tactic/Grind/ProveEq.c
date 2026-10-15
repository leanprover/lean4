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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_to_do(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(lean_object* v_a_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v_key_265_; lean_object* v_value_266_; lean_object* v_tail_267_; uint8_t v___y_269_; lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v_fst_274_; lean_object* v_snd_275_; uint8_t v___x_276_; 
v_key_265_ = lean_ctor_get(v_x_263_, 0);
v_value_266_ = lean_ctor_get(v_x_263_, 1);
v_tail_267_ = lean_ctor_get(v_x_263_, 2);
v_fst_272_ = lean_ctor_get(v_key_265_, 0);
v_snd_273_ = lean_ctor_get(v_key_265_, 1);
v_fst_274_ = lean_ctor_get(v_a_262_, 0);
v_snd_275_ = lean_ctor_get(v_a_262_, 1);
v___x_276_ = lean_expr_eqv(v_fst_272_, v_fst_274_);
if (v___x_276_ == 0)
{
v___y_269_ = v___x_276_;
goto v___jp_268_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = lean_expr_eqv(v_snd_273_, v_snd_275_);
v___y_269_ = v___x_277_;
goto v___jp_268_;
}
v___jp_268_:
{
if (v___y_269_ == 0)
{
v_x_263_ = v_tail_267_;
goto _start;
}
else
{
lean_object* v___x_271_; 
lean_inc(v_value_266_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_value_266_);
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_278_, v_x_279_);
lean_dec(v_x_279_);
lean_dec_ref(v_a_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(lean_object* v_m_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_buckets_283_; lean_object* v_fst_284_; lean_object* v_snd_285_; lean_object* v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v_fold_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_buckets_283_ = lean_ctor_get(v_m_281_, 1);
v_fst_284_ = lean_ctor_get(v_a_282_, 0);
v_snd_285_ = lean_ctor_get(v_a_282_, 1);
v___x_286_ = lean_array_get_size(v_buckets_283_);
v___x_287_ = l_Lean_Expr_hash(v_fst_284_);
v___x_288_ = l_Lean_Expr_hash(v_snd_285_);
v___x_289_ = lean_uint64_mix_hash(v___x_287_, v___x_288_);
v___x_290_ = 32ULL;
v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
v___x_293_ = 16ULL;
v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = lean_usize_of_nat(v___x_286_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
v___x_301_ = lean_array_uget_borrowed(v_buckets_283_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_282_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(lean_object* v_m_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_303_, v_a_304_);
lean_dec_ref(v_a_304_);
lean_dec_ref(v_m_303_);
return v_res_305_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object* v_a_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
else
{
lean_object* v_key_309_; lean_object* v_tail_310_; uint8_t v___y_312_; lean_object* v_fst_314_; lean_object* v_snd_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; uint8_t v___x_318_; 
v_key_309_ = lean_ctor_get(v_x_307_, 0);
v_tail_310_ = lean_ctor_get(v_x_307_, 2);
v_fst_314_ = lean_ctor_get(v_key_309_, 0);
v_snd_315_ = lean_ctor_get(v_key_309_, 1);
v_fst_316_ = lean_ctor_get(v_a_306_, 0);
v_snd_317_ = lean_ctor_get(v_a_306_, 1);
v___x_318_ = lean_expr_eqv(v_fst_314_, v_fst_316_);
if (v___x_318_ == 0)
{
v___y_312_ = v___x_318_;
goto v___jp_311_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_expr_eqv(v_snd_315_, v_snd_317_);
v___y_312_ = v___x_319_;
goto v___jp_311_;
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
v_x_307_ = v_tail_310_;
goto _start;
}
else
{
return v___y_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec_ref(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(lean_object* v_a_324_, lean_object* v_b_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_dec(v_b_325_);
lean_dec_ref(v_a_324_);
return v_x_326_;
}
else
{
lean_object* v_key_327_; lean_object* v_value_328_; lean_object* v_tail_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_348_; 
v_key_327_ = lean_ctor_get(v_x_326_, 0);
v_value_328_ = lean_ctor_get(v_x_326_, 1);
v_tail_329_ = lean_ctor_get(v_x_326_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_348_ == 0)
{
v___x_331_ = v_x_326_;
v_isShared_332_ = v_isSharedCheck_348_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_tail_329_);
lean_inc(v_value_328_);
lean_inc(v_key_327_);
lean_dec(v_x_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_348_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
uint8_t v___y_334_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; uint8_t v___x_346_; 
v_fst_342_ = lean_ctor_get(v_key_327_, 0);
v_snd_343_ = lean_ctor_get(v_key_327_, 1);
v_fst_344_ = lean_ctor_get(v_a_324_, 0);
v_snd_345_ = lean_ctor_get(v_a_324_, 1);
v___x_346_ = lean_expr_eqv(v_fst_342_, v_fst_344_);
if (v___x_346_ == 0)
{
v___y_334_ = v___x_346_;
goto v___jp_333_;
}
else
{
uint8_t v___x_347_; 
v___x_347_ = lean_expr_eqv(v_snd_343_, v_snd_345_);
v___y_334_ = v___x_347_;
goto v___jp_333_;
}
v___jp_333_:
{
if (v___y_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_324_, v_b_325_, v_tail_329_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 2, v___x_335_);
v___x_337_ = v___x_331_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_key_327_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_value_328_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
lean_object* v___x_340_; 
lean_dec(v_value_328_);
lean_dec(v_key_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v_b_325_);
lean_ctor_set(v___x_331_, 0, v_a_324_);
v___x_340_ = v___x_331_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_324_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_b_325_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_tail_329_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
return v_x_349_;
}
else
{
lean_object* v_key_351_; lean_object* v_value_352_; lean_object* v_tail_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_380_; 
v_key_351_ = lean_ctor_get(v_x_350_, 0);
v_value_352_ = lean_ctor_get(v_x_350_, 1);
v_tail_353_ = lean_ctor_get(v_x_350_, 2);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_380_ == 0)
{
v___x_355_ = v_x_350_;
v_isShared_356_ = v_isSharedCheck_380_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_tail_353_);
lean_inc(v_value_352_);
lean_inc(v_key_351_);
lean_dec(v_x_350_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_380_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_fst_357_; lean_object* v_snd_358_; lean_object* v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v_fold_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v_fst_357_ = lean_ctor_get(v_key_351_, 0);
v_snd_358_ = lean_ctor_get(v_key_351_, 1);
v___x_359_ = lean_array_get_size(v_x_349_);
v___x_360_ = l_Lean_Expr_hash(v_fst_357_);
v___x_361_ = l_Lean_Expr_hash(v_snd_358_);
v___x_362_ = lean_uint64_mix_hash(v___x_360_, v___x_361_);
v___x_363_ = 32ULL;
v___x_364_ = lean_uint64_shift_right(v___x_362_, v___x_363_);
v_fold_365_ = lean_uint64_xor(v___x_362_, v___x_364_);
v___x_366_ = 16ULL;
v___x_367_ = lean_uint64_shift_right(v_fold_365_, v___x_366_);
v___x_368_ = lean_uint64_xor(v_fold_365_, v___x_367_);
v___x_369_ = lean_uint64_to_usize(v___x_368_);
v___x_370_ = lean_usize_of_nat(v___x_359_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_sub(v___x_370_, v___x_371_);
v___x_373_ = lean_usize_land(v___x_369_, v___x_372_);
v___x_374_ = lean_array_uget_borrowed(v_x_349_, v___x_373_);
lean_inc(v___x_374_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 2, v___x_374_);
v___x_376_ = v___x_355_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_key_351_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_value_352_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v___x_374_);
v___x_376_ = v_reuseFailAlloc_379_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = lean_array_uset(v_x_349_, v___x_373_, v___x_376_);
v_x_349_ = v___x_377_;
v_x_350_ = v_tail_353_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(lean_object* v_i_381_, lean_object* v_source_382_, lean_object* v_target_383_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_array_get_size(v_source_382_);
v___x_385_ = lean_nat_dec_lt(v_i_381_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec_ref(v_source_382_);
lean_dec(v_i_381_);
return v_target_383_;
}
else
{
lean_object* v_es_386_; lean_object* v___x_387_; lean_object* v_source_388_; lean_object* v_target_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_es_386_ = lean_array_fget(v_source_382_, v_i_381_);
v___x_387_ = lean_box(0);
v_source_388_ = lean_array_fset(v_source_382_, v_i_381_, v___x_387_);
v_target_389_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_target_383_, v_es_386_);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v_i_381_, v___x_390_);
lean_dec(v_i_381_);
v_i_381_ = v___x_391_;
v_source_382_ = v_source_388_;
v_target_383_ = v_target_389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(lean_object* v_data_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_nbuckets_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_394_ = lean_array_get_size(v_data_393_);
v___x_395_ = lean_unsigned_to_nat(2u);
v_nbuckets_396_ = lean_nat_mul(v___x_394_, v___x_395_);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_box(0);
v___x_399_ = lean_mk_array(v_nbuckets_396_, v___x_398_);
v___x_400_ = lean_array_propagate_mark(v_data_393_, v___x_399_);
v___x_401_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v___x_397_, v_data_393_, v___x_400_);
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
lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_866_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_866_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_866_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_866_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
if (lean_obj_tag(v_a_751_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v___x_755_ = lean_box(0);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_object* v_val_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_865_; 
lean_del_object(v___x_753_);
v_val_759_ = lean_ctor_get(v_a_751_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_865_ == 0)
{
v___x_761_ = v_a_751_;
v_isShared_762_ = v_isSharedCheck_865_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_val_759_);
lean_dec(v_a_751_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_865_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fst_763_; uint8_t v___x_764_; 
v_fst_763_ = lean_ctor_get(v_val_759_, 0);
v___x_764_ = lean_unbox(v_fst_763_);
if (v___x_764_ == 0)
{
lean_object* v_snd_765_; 
lean_del_object(v___x_761_);
v_snd_765_ = lean_ctor_get(v_val_759_, 1);
lean_inc(v_snd_765_);
lean_dec(v_val_759_);
v___y_518_ = v_a_456_;
v___y_519_ = v_snd_765_;
v___y_520_ = v_a_458_;
v___y_521_ = v_a_459_;
v___y_522_ = v_a_460_;
v___y_523_ = v_a_461_;
v___y_524_ = v_a_462_;
v___y_525_ = v_a_463_;
v___y_526_ = v_a_464_;
v___y_527_ = v_a_465_;
v___y_528_ = v_a_466_;
v___y_529_ = v_a_467_;
goto v___jp_517_;
}
else
{
lean_object* v_snd_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_863_; 
v_snd_766_ = lean_ctor_get(v_val_759_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_val_759_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_val_759_, 0);
lean_dec(v_unused_864_);
v___x_768_ = v_val_759_;
v_isShared_769_ = v_isSharedCheck_863_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_snd_766_);
lean_dec(v_val_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_863_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v___x_770_; 
v___x_770_ = l_Lean_Expr_hasLooseBVars(v_lhs_454_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = l_Lean_Expr_hasLooseBVars(v_rhs_455_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_inc_ref(v_lhs_454_);
v___x_772_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_454_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
lean_inc_ref(v_rhs_455_);
v___x_774_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_455_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
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
v___x_776_ = lean_grind_process_to_do(v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
lean_dec_ref_known(v___x_776_, 1);
v___x_777_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_773_, v_a_775_, v_a_458_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; uint8_t v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = lean_unbox(v_a_778_);
lean_dec(v_a_778_);
if (v___x_779_ == 0)
{
lean_dec(v_a_775_);
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_del_object(v___x_761_);
v___y_518_ = v_a_456_;
v___y_519_ = v_snd_766_;
v___y_520_ = v_a_458_;
v___y_521_ = v_a_459_;
v___y_522_ = v_a_460_;
v___y_523_ = v_a_461_;
v___y_524_ = v_a_462_;
v___y_525_ = v_a_463_;
v___y_526_ = v_a_464_;
v___y_527_ = v_a_465_;
v___y_528_ = v_a_466_;
v___y_529_ = v_a_467_;
goto v___jp_517_;
}
else
{
lean_object* v___x_780_; 
lean_inc(v_a_775_);
lean_inc(v_a_773_);
v___x_780_ = l_Lean_Meta_Grind_hasSameType(v_a_773_, v_a_775_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_782_ == 0)
{
lean_dec(v_a_775_);
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_del_object(v___x_761_);
v___y_518_ = v_a_456_;
v___y_519_ = v_snd_766_;
v___y_520_ = v_a_458_;
v___y_521_ = v_a_459_;
v___y_522_ = v_a_460_;
v___y_523_ = v_a_461_;
v___y_524_ = v_a_462_;
v___y_525_ = v_a_463_;
v___y_526_ = v_a_464_;
v___y_527_ = v_a_465_;
v___y_528_ = v_a_466_;
v___y_529_ = v_a_467_;
goto v___jp_517_;
}
else
{
lean_object* v___x_783_; 
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
lean_inc(v_a_773_);
v___x_783_ = lean_infer_type(v_a_773_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_814_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_814_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_814_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_814_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_cache_788_; lean_object* v_varTypes_789_; lean_object* v_lhss_790_; lean_object* v_rhss_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_813_; 
v_cache_788_ = lean_ctor_get(v_snd_766_, 0);
v_varTypes_789_ = lean_ctor_get(v_snd_766_, 1);
v_lhss_790_ = lean_ctor_get(v_snd_766_, 2);
v_rhss_791_ = lean_ctor_get(v_snd_766_, 3);
v_isSharedCheck_813_ = !lean_is_exclusive(v_snd_766_);
if (v_isSharedCheck_813_ == 0)
{
v___x_793_ = v_snd_766_;
v_isShared_794_ = v_isSharedCheck_813_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_rhss_791_);
lean_inc(v_lhss_790_);
lean_inc(v_varTypes_789_);
lean_inc(v_cache_788_);
lean_dec(v_snd_766_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_813_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_795_ = lean_array_get_size(v_varTypes_789_);
v___x_796_ = lean_nat_add(v___x_795_, v_a_456_);
v___x_797_ = lean_array_push(v_varTypes_789_, v_a_784_);
v___x_798_ = lean_array_push(v_lhss_790_, v_a_773_);
v___x_799_ = lean_array_push(v_rhss_791_, v_a_775_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 3, v___x_799_);
lean_ctor_set(v___x_793_, 2, v___x_798_);
lean_ctor_set(v___x_793_, 1, v___x_797_);
v___x_801_ = v___x_793_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_cache_788_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v___x_799_);
v___x_801_ = v_reuseFailAlloc_812_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l_Lean_mkBVar(v___x_796_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_801_);
lean_ctor_set(v___x_768_, 0, v___x_802_);
v___x_804_ = v___x_768_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_801_);
v___x_804_ = v_reuseFailAlloc_811_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_804_);
v___x_806_ = v___x_761_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_806_);
v___x_808_ = v___x_786_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
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
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_a_775_);
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_del_object(v___x_761_);
v_a_815_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_783_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_783_);
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
lean_dec(v_a_775_);
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_del_object(v___x_761_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_823_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_780_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_780_);
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
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_775_);
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_del_object(v___x_761_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_831_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_777_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_777_);
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
lean_dec(v_a_775_);
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_del_object(v___x_761_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_839_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_776_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_776_);
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
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_a_773_);
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_del_object(v___x_761_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_847_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_774_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_774_);
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
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_del_object(v___x_761_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_855_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_772_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_772_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_del_object(v___x_768_);
lean_del_object(v___x_761_);
v___y_518_ = v_a_456_;
v___y_519_ = v_snd_766_;
v___y_520_ = v_a_458_;
v___y_521_ = v_a_459_;
v___y_522_ = v_a_460_;
v___y_523_ = v_a_461_;
v___y_524_ = v_a_462_;
v___y_525_ = v_a_463_;
v___y_526_ = v_a_464_;
v___y_527_ = v_a_465_;
v___y_528_ = v_a_466_;
v___y_529_ = v_a_467_;
goto v___jp_517_;
}
}
else
{
lean_del_object(v___x_768_);
lean_del_object(v___x_761_);
v___y_518_ = v_a_456_;
v___y_519_ = v_snd_766_;
v___y_520_ = v_a_458_;
v___y_521_ = v_a_459_;
v___y_522_ = v_a_460_;
v___y_523_ = v_a_461_;
v___y_524_ = v_a_462_;
v___y_525_ = v_a_463_;
v___y_526_ = v_a_464_;
v___y_527_ = v_a_465_;
v___y_528_ = v_a_466_;
v___y_529_ = v_a_467_;
goto v___jp_517_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_867_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_750_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_750_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
v___jp_469_:
{
if (v___y_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v___y_485_);
lean_dec(v___y_481_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_473_);
lean_dec_ref(v___y_472_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_485_, v___y_472_, v___y_476_, v___y_473_, v___y_474_, v___y_483_, v___y_470_, v___y_471_, v___y_477_, v___y_484_, v___y_479_, v___y_480_, v___y_482_, v___y_475_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
if (lean_obj_tag(v_a_490_) == 0)
{
lean_dec(v___y_481_);
lean_dec(v___y_478_);
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
v___x_503_ = l_Lean_Expr_proj___override(v___y_478_, v___y_481_, v_fst_498_);
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
lean_dec(v___y_481_);
lean_dec(v___y_478_);
return v___x_489_;
}
}
}
v___jp_517_:
{
switch(lean_obj_tag(v_lhs_454_))
{
case 5:
{
if (lean_obj_tag(v_rhs_455_) == 5)
{
lean_object* v_fn_530_; lean_object* v_arg_531_; lean_object* v_fn_532_; lean_object* v_arg_533_; lean_object* v___x_534_; 
v_fn_530_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc_ref(v_fn_530_);
v_arg_531_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_arg_531_);
lean_dec_ref_known(v_lhs_454_, 2);
v_fn_532_ = lean_ctor_get(v_rhs_455_, 0);
lean_inc_ref(v_fn_532_);
v_arg_533_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_arg_533_);
lean_dec_ref_known(v_rhs_455_, 2);
v___x_534_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_fn_530_, v_fn_532_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
if (lean_obj_tag(v_a_535_) == 0)
{
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_531_);
return v___x_534_;
}
else
{
lean_object* v_val_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_539_; 
lean_inc_ref(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v_val_536_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_a_535_, 1);
v_fst_537_ = lean_ctor_get(v_val_536_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v_val_536_, 1);
lean_inc(v_snd_538_);
lean_dec(v_val_536_);
v___x_539_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_arg_531_, v_arg_533_, v___y_518_, v_snd_538_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
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
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref_known(v_lhs_454_, 2);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
case 6:
{
if (lean_obj_tag(v_rhs_455_) == 6)
{
lean_object* v_binderName_569_; lean_object* v_binderType_570_; lean_object* v_body_571_; uint8_t v_binderInfo_572_; lean_object* v_binderType_573_; lean_object* v_body_574_; lean_object* v___x_575_; 
v_binderName_569_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_binderName_569_);
v_binderType_570_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_binderType_570_);
v_body_571_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_body_571_);
v_binderInfo_572_ = lean_ctor_get_uint8(v_lhs_454_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_454_, 3);
v_binderType_573_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_binderType_573_);
v_body_574_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_body_574_);
lean_dec_ref_known(v_rhs_455_, 3);
v___x_575_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_570_, v_binderType_573_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
if (lean_obj_tag(v_a_576_) == 0)
{
lean_dec_ref(v_body_574_);
lean_dec_ref(v_body_571_);
lean_dec(v_binderName_569_);
return v___x_575_;
}
else
{
lean_object* v_val_577_; lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_inc_ref(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v_val_577_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v_a_576_, 1);
v_fst_578_ = lean_ctor_get(v_val_577_, 0);
lean_inc(v_fst_578_);
v_snd_579_ = lean_ctor_get(v_val_577_, 1);
lean_inc(v_snd_579_);
lean_dec(v_val_577_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v___y_518_, v___x_580_);
v___x_582_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_571_, v_body_574_, v___x_581_, v_snd_579_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
if (lean_obj_tag(v_a_583_) == 0)
{
lean_dec(v_fst_578_);
lean_dec(v_binderName_569_);
return v___x_582_;
}
else
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_609_);
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_608_;
goto v_resetjp_584_;
}
else
{
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_608_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_val_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_607_; 
v_val_587_ = lean_ctor_get(v_a_583_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_583_);
if (v_isSharedCheck_607_ == 0)
{
v___x_589_ = v_a_583_;
v_isShared_590_ = v_isSharedCheck_607_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_val_587_);
lean_dec(v_a_583_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_607_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
v_fst_591_ = lean_ctor_get(v_val_587_, 0);
v_snd_592_ = lean_ctor_get(v_val_587_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_val_587_);
if (v_isSharedCheck_606_ == 0)
{
v___x_594_ = v_val_587_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
lean_dec(v_val_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_mkLambda(v_binderName_569_, v_binderInfo_572_, v_fst_578_, v_fst_591_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_snd_592_);
v___x_598_ = v_reuseFailAlloc_605_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_598_);
v___x_600_ = v___x_589_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_600_);
v___x_602_ = v___x_585_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
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
lean_dec(v_fst_578_);
lean_dec(v_binderName_569_);
return v___x_582_;
}
}
}
else
{
lean_dec_ref(v_body_574_);
lean_dec_ref(v_body_571_);
lean_dec(v_binderName_569_);
return v___x_575_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec_ref_known(v_lhs_454_, 3);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
case 7:
{
if (lean_obj_tag(v_rhs_455_) == 7)
{
lean_object* v_binderName_612_; lean_object* v_binderType_613_; lean_object* v_body_614_; uint8_t v_binderInfo_615_; lean_object* v_binderType_616_; lean_object* v_body_617_; lean_object* v___x_618_; 
v_binderName_612_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_binderName_612_);
v_binderType_613_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_binderType_613_);
v_body_614_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_body_614_);
v_binderInfo_615_ = lean_ctor_get_uint8(v_lhs_454_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_454_, 3);
v_binderType_616_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_binderType_616_);
v_body_617_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_body_617_);
lean_dec_ref_known(v_rhs_455_, 3);
v___x_618_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_613_, v_binderType_616_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
if (lean_obj_tag(v_a_619_) == 0)
{
lean_dec_ref(v_body_617_);
lean_dec_ref(v_body_614_);
lean_dec(v_binderName_612_);
return v___x_618_;
}
else
{
lean_object* v_val_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_inc_ref(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v_val_620_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v_a_619_, 1);
v_fst_621_ = lean_ctor_get(v_val_620_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v_val_620_, 1);
lean_inc(v_snd_622_);
lean_dec(v_val_620_);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v___y_518_, v___x_623_);
v___x_625_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_614_, v_body_617_, v___x_624_, v_snd_622_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_624_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
if (lean_obj_tag(v_a_626_) == 0)
{
lean_dec(v_fst_621_);
lean_dec(v_binderName_612_);
return v___x_625_;
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_625_, 0);
lean_dec(v_unused_652_);
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_651_;
goto v_resetjp_627_;
}
else
{
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_651_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_val_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_650_; 
v_val_630_ = lean_ctor_get(v_a_626_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_626_);
if (v_isSharedCheck_650_ == 0)
{
v___x_632_ = v_a_626_;
v_isShared_633_ = v_isSharedCheck_650_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_val_630_);
lean_dec(v_a_626_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_650_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_fst_634_; lean_object* v_snd_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_649_; 
v_fst_634_ = lean_ctor_get(v_val_630_, 0);
v_snd_635_ = lean_ctor_get(v_val_630_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_val_630_);
if (v_isSharedCheck_649_ == 0)
{
v___x_637_ = v_val_630_;
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_snd_635_);
lean_inc(v_fst_634_);
lean_dec(v_val_630_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_mkForall(v_binderName_612_, v_binderInfo_615_, v_fst_621_, v_fst_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_snd_635_);
v___x_641_ = v_reuseFailAlloc_648_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_641_);
v___x_643_ = v___x_632_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_643_);
v___x_645_ = v___x_628_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
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
lean_dec(v_fst_621_);
lean_dec(v_binderName_612_);
return v___x_625_;
}
}
}
else
{
lean_dec_ref(v_body_617_);
lean_dec_ref(v_body_614_);
lean_dec(v_binderName_612_);
return v___x_618_;
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v_lhs_454_, 3);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
case 8:
{
if (lean_obj_tag(v_rhs_455_) == 8)
{
lean_object* v_declName_655_; lean_object* v_type_656_; lean_object* v_value_657_; lean_object* v_body_658_; uint8_t v_nondep_659_; lean_object* v_type_660_; lean_object* v_value_661_; lean_object* v_body_662_; lean_object* v___x_663_; 
v_declName_655_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_declName_655_);
v_type_656_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_type_656_);
v_value_657_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_value_657_);
v_body_658_ = lean_ctor_get(v_lhs_454_, 3);
lean_inc_ref(v_body_658_);
v_nondep_659_ = lean_ctor_get_uint8(v_lhs_454_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_lhs_454_, 4);
v_type_660_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_type_660_);
v_value_661_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_value_661_);
v_body_662_ = lean_ctor_get(v_rhs_455_, 3);
lean_inc_ref(v_body_662_);
lean_dec_ref_known(v_rhs_455_, 4);
v___x_663_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_type_656_, v_type_660_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
if (lean_obj_tag(v_a_664_) == 0)
{
lean_dec_ref(v_body_662_);
lean_dec_ref(v_value_661_);
lean_dec_ref(v_body_658_);
lean_dec_ref(v_value_657_);
lean_dec(v_declName_655_);
return v___x_663_;
}
else
{
lean_object* v_val_665_; lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_668_; 
lean_inc_ref(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v_val_665_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v_a_664_, 1);
v_fst_666_ = lean_ctor_get(v_val_665_, 0);
lean_inc(v_fst_666_);
v_snd_667_ = lean_ctor_get(v_val_665_, 1);
lean_inc(v_snd_667_);
lean_dec(v_val_665_);
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_value_657_, v_value_661_, v___y_518_, v_snd_667_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
if (lean_obj_tag(v_a_669_) == 0)
{
lean_dec(v_fst_666_);
lean_dec_ref(v_body_662_);
lean_dec_ref(v_body_658_);
lean_dec(v_declName_655_);
return v___x_668_;
}
else
{
lean_object* v_val_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc_ref(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v_val_670_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_a_669_, 1);
v_fst_671_ = lean_ctor_get(v_val_670_, 0);
lean_inc(v_fst_671_);
v_snd_672_ = lean_ctor_get(v_val_670_, 1);
lean_inc(v_snd_672_);
lean_dec(v_val_670_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v___y_518_, v___x_673_);
v___x_675_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_658_, v_body_662_, v___x_674_, v_snd_672_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
if (lean_obj_tag(v_a_676_) == 0)
{
lean_dec(v_fst_671_);
lean_dec(v_fst_666_);
lean_dec(v_declName_655_);
return v___x_675_;
}
else
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_701_; 
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_675_, 0);
lean_dec(v_unused_702_);
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_701_;
goto v_resetjp_677_;
}
else
{
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_701_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_700_; 
v_val_680_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_700_ == 0)
{
v___x_682_ = v_a_676_;
v_isShared_683_ = v_isSharedCheck_700_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_a_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_700_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_699_; 
v_fst_684_ = lean_ctor_get(v_val_680_, 0);
v_snd_685_ = lean_ctor_get(v_val_680_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_val_680_);
if (v_isSharedCheck_699_ == 0)
{
v___x_687_ = v_val_680_;
v_isShared_688_ = v_isSharedCheck_699_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_inc(v_fst_684_);
lean_dec(v_val_680_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_699_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Lean_Expr_letE___override(v_declName_655_, v_fst_666_, v_fst_671_, v_fst_684_, v_nondep_659_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_685_);
v___x_691_ = v_reuseFailAlloc_698_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_691_);
v___x_693_ = v___x_682_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_693_);
v___x_695_ = v___x_678_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
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
lean_dec(v_fst_671_);
lean_dec(v_fst_666_);
lean_dec(v_declName_655_);
return v___x_675_;
}
}
}
else
{
lean_dec(v_fst_666_);
lean_dec_ref(v_body_662_);
lean_dec_ref(v_body_658_);
lean_dec(v_declName_655_);
return v___x_668_;
}
}
}
else
{
lean_dec_ref(v_body_662_);
lean_dec_ref(v_value_661_);
lean_dec_ref(v_body_658_);
lean_dec_ref(v_value_657_);
lean_dec(v_declName_655_);
return v___x_663_;
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref_known(v_lhs_454_, 4);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
case 10:
{
if (lean_obj_tag(v_rhs_455_) == 10)
{
lean_object* v_data_705_; lean_object* v_expr_706_; lean_object* v_expr_707_; lean_object* v___x_708_; 
v_data_705_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_data_705_);
v_expr_706_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc_ref(v_expr_706_);
lean_dec_ref_known(v_lhs_454_, 2);
v_expr_707_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc_ref(v_expr_707_);
lean_dec_ref_known(v_rhs_455_, 2);
v___x_708_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_expr_706_, v_expr_707_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
if (lean_obj_tag(v_a_709_) == 0)
{
lean_dec(v_data_705_);
return v___x_708_;
}
else
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_734_; 
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_708_, 0);
lean_dec(v_unused_735_);
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_734_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_734_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_val_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_733_; 
v_val_713_ = lean_ctor_get(v_a_709_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_733_ == 0)
{
v___x_715_ = v_a_709_;
v_isShared_716_ = v_isSharedCheck_733_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_val_713_);
lean_dec(v_a_709_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_733_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_732_; 
v_fst_717_ = lean_ctor_get(v_val_713_, 0);
v_snd_718_ = lean_ctor_get(v_val_713_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_val_713_);
if (v_isSharedCheck_732_ == 0)
{
v___x_720_ = v_val_713_;
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
lean_dec(v_val_713_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = l_Lean_Expr_mdata___override(v_data_705_, v_fst_717_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_snd_718_);
v___x_724_ = v_reuseFailAlloc_731_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_724_);
v___x_726_ = v___x_715_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_726_);
v___x_728_ = v___x_711_;
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
}
}
}
}
}
else
{
lean_dec(v_data_705_);
return v___x_708_;
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref_known(v_lhs_454_, 2);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
case 11:
{
if (lean_obj_tag(v_rhs_455_) == 11)
{
lean_object* v_typeName_738_; lean_object* v_idx_739_; lean_object* v_struct_740_; lean_object* v_typeName_741_; lean_object* v_idx_742_; lean_object* v_struct_743_; uint8_t v___x_744_; 
v_typeName_738_ = lean_ctor_get(v_lhs_454_, 0);
lean_inc(v_typeName_738_);
v_idx_739_ = lean_ctor_get(v_lhs_454_, 1);
lean_inc(v_idx_739_);
v_struct_740_ = lean_ctor_get(v_lhs_454_, 2);
lean_inc_ref(v_struct_740_);
lean_dec_ref_known(v_lhs_454_, 3);
v_typeName_741_ = lean_ctor_get(v_rhs_455_, 0);
lean_inc(v_typeName_741_);
v_idx_742_ = lean_ctor_get(v_rhs_455_, 1);
lean_inc(v_idx_742_);
v_struct_743_ = lean_ctor_get(v_rhs_455_, 2);
lean_inc_ref(v_struct_743_);
lean_dec_ref_known(v_rhs_455_, 3);
v___x_744_ = lean_name_eq(v_typeName_738_, v_typeName_741_);
lean_dec(v_typeName_741_);
if (v___x_744_ == 0)
{
lean_dec(v_idx_742_);
v___y_470_ = v___y_522_;
v___y_471_ = v___y_523_;
v___y_472_ = v_struct_743_;
v___y_473_ = v___y_519_;
v___y_474_ = v___y_520_;
v___y_475_ = v___y_529_;
v___y_476_ = v___y_518_;
v___y_477_ = v___y_524_;
v___y_478_ = v_typeName_738_;
v___y_479_ = v___y_526_;
v___y_480_ = v___y_527_;
v___y_481_ = v_idx_739_;
v___y_482_ = v___y_528_;
v___y_483_ = v___y_521_;
v___y_484_ = v___y_525_;
v___y_485_ = v_struct_740_;
v___y_486_ = v___x_744_;
goto v___jp_469_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_eq(v_idx_739_, v_idx_742_);
lean_dec(v_idx_742_);
v___y_470_ = v___y_522_;
v___y_471_ = v___y_523_;
v___y_472_ = v_struct_743_;
v___y_473_ = v___y_519_;
v___y_474_ = v___y_520_;
v___y_475_ = v___y_529_;
v___y_476_ = v___y_518_;
v___y_477_ = v___y_524_;
v___y_478_ = v_typeName_738_;
v___y_479_ = v___y_526_;
v___y_480_ = v___y_527_;
v___y_481_ = v_idx_739_;
v___y_482_ = v___y_528_;
v___y_483_ = v___y_521_;
v___y_484_ = v___y_525_;
v___y_485_ = v_struct_740_;
v___y_486_ = v___x_745_;
goto v___jp_469_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref_known(v_lhs_454_, 3);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
default: 
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v___y_519_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object* v_lhs_875_, lean_object* v_rhs_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
size_t v___x_890_; size_t v___x_891_; uint8_t v___x_892_; 
v___x_890_ = lean_ptr_addr(v_lhs_875_);
v___x_891_ = lean_ptr_addr(v_rhs_876_);
v___x_892_ = lean_usize_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v_cache_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_cache_893_ = lean_ctor_get(v_a_878_, 0);
lean_inc_ref(v_rhs_876_);
lean_inc_ref(v_lhs_875_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_lhs_875_);
lean_ctor_set(v___x_894_, 1, v_rhs_876_);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_893_, v___x_894_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref_known(v___x_894_, 2);
lean_dec_ref(v_rhs_876_);
lean_dec_ref(v_lhs_875_);
v_val_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_905_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_905_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_val_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_905_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_val_896_);
lean_ctor_set(v___x_900_, 1, v_a_878_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_900_);
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_904_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
else
{
lean_object* v___x_906_; 
lean_dec(v___x_895_);
v___x_906_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_875_, v_rhs_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
if (lean_obj_tag(v_a_907_) == 0)
{
lean_dec_ref_known(v___x_894_, 2);
return v___x_906_;
}
else
{
lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_906_, 0);
lean_dec(v_unused_944_);
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_943_;
goto v_resetjp_908_;
}
else
{
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_943_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_val_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_942_; 
v_val_911_ = lean_ctor_get(v_a_907_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_942_ == 0)
{
v___x_913_ = v_a_907_;
v_isShared_914_ = v_isSharedCheck_942_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_val_911_);
lean_dec(v_a_907_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_942_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_snd_915_; lean_object* v_fst_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_941_; 
v_snd_915_ = lean_ctor_get(v_val_911_, 1);
v_fst_916_ = lean_ctor_get(v_val_911_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v_val_911_);
if (v_isSharedCheck_941_ == 0)
{
v___x_918_ = v_val_911_;
v_isShared_919_ = v_isSharedCheck_941_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_915_);
lean_inc(v_fst_916_);
lean_dec(v_val_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_941_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_cache_920_; lean_object* v_varTypes_921_; lean_object* v_lhss_922_; lean_object* v_rhss_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_940_; 
v_cache_920_ = lean_ctor_get(v_snd_915_, 0);
v_varTypes_921_ = lean_ctor_get(v_snd_915_, 1);
v_lhss_922_ = lean_ctor_get(v_snd_915_, 2);
v_rhss_923_ = lean_ctor_get(v_snd_915_, 3);
v_isSharedCheck_940_ = !lean_is_exclusive(v_snd_915_);
if (v_isSharedCheck_940_ == 0)
{
v___x_925_ = v_snd_915_;
v_isShared_926_ = v_isSharedCheck_940_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_rhss_923_);
lean_inc(v_lhss_922_);
lean_inc(v_varTypes_921_);
lean_inc(v_cache_920_);
lean_dec(v_snd_915_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_940_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
lean_inc(v_fst_916_);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_920_, v___x_894_, v_fst_916_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_varTypes_921_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_lhss_922_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_rhss_923_);
v___x_929_ = v_reuseFailAlloc_939_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_929_);
v___x_931_ = v___x_918_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_916_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_929_);
v___x_931_ = v_reuseFailAlloc_938_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_931_);
v___x_933_ = v___x_913_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_933_);
v___x_935_ = v___x_909_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
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
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_894_, 2);
return v___x_906_;
}
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref(v_rhs_876_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_lhs_875_);
lean_ctor_set(v___x_945_, 1, v_a_878_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object* v_lhs_948_, lean_object* v_rhs_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_948_, v_rhs_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
lean_dec(v_a_950_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object* v_lhs_964_, lean_object* v_rhs_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_964_, v_rhs_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_966_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(lean_object* v_00_u03b2_980_, lean_object* v_m_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_981_, v_a_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(lean_object* v_00_u03b2_984_, lean_object* v_m_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(v_00_u03b2_984_, v_m_985_, v_a_986_);
lean_dec_ref(v_a_986_);
lean_dec_ref(v_m_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object* v_00_u03b2_988_, lean_object* v_m_989_, lean_object* v_a_990_, lean_object* v_b_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_989_, v_a_990_, v_b_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_997_, lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(v_00_u03b2_997_, v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
return v_res_1000_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object* v_00_u03b2_1001_, lean_object* v_a_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_a_1006_, lean_object* v_x_1007_){
_start:
{
uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_res_1008_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_1005_, v_a_1006_, v_x_1007_);
lean_dec(v_x_1007_);
lean_dec_ref(v_a_1006_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(lean_object* v_00_u03b2_1010_, lean_object* v_data_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_data_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(lean_object* v_00_u03b2_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_1014_, v_b_1015_, v_x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1018_, lean_object* v_i_1019_, lean_object* v_source_1020_, lean_object* v_target_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v_i_1019_, v_source_1020_, v_target_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1024_, v_x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_unsigned_to_nat(16u);
v___x_1029_ = lean_mk_array(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2));
v___x_1036_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
v___x_1037_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
lean_ctor_set(v___x_1037_, 2, v___x_1035_);
lean_ctor_set(v___x_1037_, 3, v___x_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object* v_lhs_1045_, lean_object* v_rhs_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_Sym_shareCommon(v_lhs_1045_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = l_Lean_Meta_Sym_shareCommon(v_rhs_1046_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_1059_, v_a_1061_, v___x_1062_, v___x_1063_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1134_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1134_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1134_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
if (lean_obj_tag(v_a_1065_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1129_; 
v_val_1069_ = lean_ctor_get(v_a_1065_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1065_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1071_ = v_a_1065_;
v_isShared_1072_ = v_isSharedCheck_1129_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v_a_1065_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1129_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_snd_1073_; lean_object* v_fst_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1128_; 
v_snd_1073_ = lean_ctor_get(v_val_1069_, 1);
v_fst_1074_ = lean_ctor_get(v_val_1069_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_val_1069_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1076_ = v_val_1069_;
v_isShared_1077_ = v_isSharedCheck_1128_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1073_);
lean_inc(v_fst_1074_);
lean_dec(v_val_1069_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1128_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_varTypes_1078_; lean_object* v_lhss_1079_; lean_object* v_rhss_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_varTypes_1078_ = lean_ctor_get(v_snd_1073_, 1);
lean_inc_ref(v_varTypes_1078_);
v_lhss_1079_ = lean_ctor_get(v_snd_1073_, 2);
lean_inc_ref(v_lhss_1079_);
v_rhss_1080_ = lean_ctor_get(v_snd_1073_, 3);
lean_inc_ref(v_rhss_1080_);
lean_dec(v_snd_1073_);
v___x_1081_ = lean_array_get_size(v_lhss_1079_);
v___x_1082_ = lean_nat_dec_eq(v___x_1081_, v___x_1062_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_del_object(v___x_1067_);
v___x_1083_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_1078_, v_fst_1074_);
lean_dec_ref(v_varTypes_1078_);
lean_inc(v_a_1056_);
lean_inc_ref(v_a_1055_);
lean_inc(v_a_1054_);
lean_inc_ref(v_a_1053_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = lean_infer_type(v___x_1083_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_n(v_a_1085_, 2);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_Meta_getLevel(v_a_1085_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1107_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1107_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1107_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7));
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_a_1087_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_Expr_const___override(v___x_1091_, v___x_1093_);
v___x_1095_ = l_Lean_mkAppB(v___x_1094_, v_a_1085_, v___x_1083_);
lean_inc_ref(v___x_1095_);
v___x_1096_ = l_Lean_mkAppN(v___x_1095_, v_lhss_1079_);
lean_dec_ref(v_lhss_1079_);
v___x_1097_ = l_Lean_mkAppN(v___x_1095_, v_rhss_1080_);
lean_dec_ref(v_rhss_1080_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1097_);
lean_ctor_set(v___x_1076_, 0, v___x_1096_);
v___x_1099_ = v___x_1076_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1099_);
v___x_1101_ = v___x_1071_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1101_);
v___x_1103_ = v___x_1089_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1085_);
lean_dec_ref(v___x_1083_);
lean_dec_ref(v_rhss_1080_);
lean_dec_ref(v_lhss_1079_);
lean_del_object(v___x_1076_);
lean_del_object(v___x_1071_);
v_a_1108_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1086_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1086_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v___x_1083_);
lean_dec_ref(v_rhss_1080_);
lean_dec_ref(v_lhss_1079_);
lean_del_object(v___x_1076_);
lean_del_object(v___x_1071_);
v_a_1116_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1084_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1084_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec_ref(v_rhss_1080_);
lean_dec_ref(v_lhss_1079_);
lean_dec_ref(v_varTypes_1078_);
lean_del_object(v___x_1076_);
lean_dec(v_fst_1074_);
lean_del_object(v___x_1071_);
v___x_1124_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1124_);
v___x_1126_ = v___x_1067_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
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
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v_a_1065_);
v___x_1130_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1130_);
v___x_1132_ = v___x_1067_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
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
v_a_1135_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1064_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1064_);
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
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_1059_);
v_a_1143_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1060_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1060_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v_rhs_1046_);
v_a_1151_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1058_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1058_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object* v_lhs_1159_, lean_object* v_rhs_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_1159_, v_rhs_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec(v_a_1161_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(lean_object* v_msgData_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_env_1180_; uint8_t v___x_1181_; lean_object* v_env_1182_; lean_object* v___x_1183_; lean_object* v_toCold_1184_; lean_object* v_mctx_1185_; lean_object* v_lctx_1186_; lean_object* v_options_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1179_ = lean_st_ref_get(v___y_1177_);
v_env_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_env_1180_);
lean_dec(v___x_1179_);
v___x_1181_ = 0;
v_env_1182_ = l_Lean_Environment_setRecordingDeps(v_env_1180_, v___x_1181_);
v___x_1183_ = lean_st_ref_get(v___y_1175_);
v_toCold_1184_ = lean_ctor_get(v___y_1176_, 0);
v_mctx_1185_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_mctx_1185_);
lean_dec(v___x_1183_);
v_lctx_1186_ = lean_ctor_get(v___y_1174_, 2);
v_options_1187_ = lean_ctor_get(v_toCold_1184_, 2);
lean_inc_ref(v_options_1187_);
lean_inc_ref(v_lctx_1186_);
v___x_1188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1188_, 0, v_env_1182_);
lean_ctor_set(v___x_1188_, 1, v_mctx_1185_);
lean_ctor_set(v___x_1188_, 2, v_lctx_1186_);
lean_ctor_set(v___x_1188_, 3, v_options_1187_);
v___x_1189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v_msgData_1173_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(lean_object* v_msgData_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1197_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1198_; double v___x_1199_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_float_of_nat(v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object* v_cls_1203_, lean_object* v_msg_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_ref_1210_; lean_object* v___x_1211_; lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1257_; 
v_ref_1210_ = lean_ctor_get(v___y_1207_, 2);
v___x_1211_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1257_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1257_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v_traceState_1217_; lean_object* v_env_1218_; lean_object* v_nextMacroScope_1219_; lean_object* v_ngen_1220_; lean_object* v_auxDeclNGen_1221_; lean_object* v_cache_1222_; lean_object* v_recordedDeps_1223_; lean_object* v_messages_1224_; lean_object* v_infoState_1225_; lean_object* v_snapshotTasks_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1256_; 
v___x_1216_ = lean_st_ref_take(v___y_1208_);
v_traceState_1217_ = lean_ctor_get(v___x_1216_, 4);
v_env_1218_ = lean_ctor_get(v___x_1216_, 0);
v_nextMacroScope_1219_ = lean_ctor_get(v___x_1216_, 1);
v_ngen_1220_ = lean_ctor_get(v___x_1216_, 2);
v_auxDeclNGen_1221_ = lean_ctor_get(v___x_1216_, 3);
v_cache_1222_ = lean_ctor_get(v___x_1216_, 5);
v_recordedDeps_1223_ = lean_ctor_get(v___x_1216_, 6);
v_messages_1224_ = lean_ctor_get(v___x_1216_, 7);
v_infoState_1225_ = lean_ctor_get(v___x_1216_, 8);
v_snapshotTasks_1226_ = lean_ctor_get(v___x_1216_, 9);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1228_ = v___x_1216_;
v_isShared_1229_ = v_isSharedCheck_1256_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snapshotTasks_1226_);
lean_inc(v_infoState_1225_);
lean_inc(v_messages_1224_);
lean_inc(v_recordedDeps_1223_);
lean_inc(v_cache_1222_);
lean_inc(v_traceState_1217_);
lean_inc(v_auxDeclNGen_1221_);
lean_inc(v_ngen_1220_);
lean_inc(v_nextMacroScope_1219_);
lean_inc(v_env_1218_);
lean_dec(v___x_1216_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1256_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
uint64_t v_tid_1230_; lean_object* v_traces_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1255_; 
v_tid_1230_ = lean_ctor_get_uint64(v_traceState_1217_, sizeof(void*)*1);
v_traces_1231_ = lean_ctor_get(v_traceState_1217_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_traceState_1217_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1233_ = v_traceState_1217_;
v_isShared_1234_ = v_isSharedCheck_1255_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_traces_1231_);
lean_dec(v_traceState_1217_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1255_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; double v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
v___x_1238_ = 0;
v___x_1239_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1));
v___x_1240_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1240_, 0, v_cls_1203_);
lean_ctor_set(v___x_1240_, 1, v___x_1236_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
lean_ctor_set_float(v___x_1240_, sizeof(void*)*3, v___x_1237_);
lean_ctor_set_float(v___x_1240_, sizeof(void*)*3 + 8, v___x_1237_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*3 + 16, v___x_1238_);
v___x_1241_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2));
v___x_1242_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v_a_1212_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
lean_inc(v_ref_1210_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_ref_1210_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_PersistentArray_push___redArg(v_traces_1231_, v___x_1243_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1244_);
v___x_1246_ = v___x_1233_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1244_);
lean_ctor_set_uint64(v_reuseFailAlloc_1254_, sizeof(void*)*1, v_tid_1230_);
v___x_1246_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1248_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 4, v___x_1246_);
v___x_1248_ = v___x_1228_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_env_1218_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_nextMacroScope_1219_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_ngen_1220_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_auxDeclNGen_1221_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1253_, 5, v_cache_1222_);
lean_ctor_set(v_reuseFailAlloc_1253_, 6, v_recordedDeps_1223_);
lean_ctor_set(v_reuseFailAlloc_1253_, 7, v_messages_1224_);
lean_ctor_set(v_reuseFailAlloc_1253_, 8, v_infoState_1225_);
lean_ctor_set(v_reuseFailAlloc_1253_, 9, v_snapshotTasks_1226_);
v___x_1248_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_st_ref_put(v___y_1208_, v___x_1248_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1235_);
v___x_1251_ = v___x_1214_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1235_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object* v_cls_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1258_, v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5));
v___x_1278_ = l_Lean_Name_append(v___x_1277_, v___x_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object* v_lhs_u2080_1288_, lean_object* v_rhs_u2080_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_1288_, v_rhs_u2080_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1427_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1427_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1427_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
if (lean_obj_tag(v_a_1302_) == 1)
{
lean_object* v_val_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1304_);
v_val_1306_ = lean_ctor_get(v_a_1302_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_a_1302_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1308_ = v_a_1302_;
v_isShared_1309_ = v_isSharedCheck_1422_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_val_1306_);
lean_dec(v_a_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1422_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1421_; 
v_fst_1310_ = lean_ctor_get(v_val_1306_, 0);
v_snd_1311_ = lean_ctor_get(v_val_1306_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_val_1306_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1313_ = v_val_1306_;
v_isShared_1314_ = v_isSharedCheck_1421_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1311_);
lean_inc(v_fst_1310_);
lean_dec(v_val_1306_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1421_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v_toCold_1394_; lean_object* v_options_1395_; uint8_t v_hasTrace_1396_; 
v_toCold_1394_ = lean_ctor_get(v_a_1298_, 0);
v_options_1395_ = lean_ctor_get(v_toCold_1394_, 2);
v_hasTrace_1396_ = lean_ctor_get_uint8(v_options_1395_, sizeof(void*)*1);
if (v_hasTrace_1396_ == 0)
{
lean_del_object(v___x_1313_);
v___y_1316_ = v_a_1290_;
v___y_1317_ = v_a_1291_;
v___y_1318_ = v_a_1292_;
v___y_1319_ = v_a_1293_;
v___y_1320_ = v_a_1294_;
v___y_1321_ = v_a_1295_;
v___y_1322_ = v_a_1296_;
v___y_1323_ = v_a_1297_;
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
goto v___jp_1315_;
}
else
{
lean_object* v_inheritedTraceOptions_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_inheritedTraceOptions_1397_ = lean_ctor_get(v_toCold_1394_, 11);
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1400_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1397_, v_options_1395_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_del_object(v___x_1313_);
v___y_1316_ = v_a_1290_;
v___y_1317_ = v_a_1291_;
v___y_1318_ = v_a_1292_;
v___y_1319_ = v_a_1293_;
v___y_1320_ = v_a_1294_;
v___y_1321_ = v_a_1295_;
v___y_1322_ = v_a_1296_;
v___y_1323_ = v_a_1297_;
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
lean_inc(v_fst_1310_);
v___x_1402_ = l_Lean_MessageData_ofExpr(v_fst_1310_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 7);
lean_ctor_set(v___x_1313_, 1, v___x_1402_);
lean_ctor_set(v___x_1313_, 0, v___x_1401_);
v___x_1404_ = v___x_1313_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
lean_inc(v_snd_1311_);
v___x_1407_ = l_Lean_MessageData_ofExpr(v_snd_1311_);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_1398_, v___x_1410_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref_known(v___x_1411_, 1);
v___y_1316_ = v_a_1290_;
v___y_1317_ = v_a_1291_;
v___y_1318_ = v_a_1292_;
v___y_1319_ = v_a_1293_;
v___y_1320_ = v_a_1294_;
v___y_1321_ = v_a_1295_;
v___y_1322_ = v_a_1296_;
v___y_1323_ = v_a_1297_;
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
goto v___jp_1315_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_snd_1311_);
lean_dec(v_fst_1310_);
lean_del_object(v___x_1308_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1326_; 
v___x_1326_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_1310_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_1311_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
lean_inc(v___y_1316_);
v___x_1330_ = lean_grind_process_to_do(v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v___x_1331_; 
lean_dec_ref_known(v___x_1330_, 1);
v___x_1331_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1327_, v_a_1329_, v___y_1316_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1361_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1361_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1361_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_unbox(v_a_1332_);
lean_dec(v_a_1332_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_dec(v_a_1329_);
lean_dec(v_a_1327_);
lean_del_object(v___x_1308_);
v___x_1337_ = lean_box(0);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_object* v___x_1341_; 
lean_del_object(v___x_1334_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
lean_inc(v___y_1316_);
v___x_1341_ = lean_grind_mk_eq_proof(v_a_1327_, v_a_1329_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_a_1342_);
v___x_1347_ = v___x_1308_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_del_object(v___x_1308_);
v_a_1353_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1341_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1341_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
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
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1329_);
lean_dec(v_a_1327_);
lean_del_object(v___x_1308_);
v_a_1362_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1331_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1331_);
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
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1329_);
lean_dec(v_a_1327_);
lean_del_object(v___x_1308_);
v_a_1370_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1330_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1330_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_a_1327_);
lean_del_object(v___x_1308_);
v_a_1378_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1328_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1328_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_snd_1311_);
lean_del_object(v___x_1308_);
v_a_1386_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1326_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1326_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_dec(v_a_1302_);
v___x_1423_ = lean_box(0);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1423_);
v___x_1425_ = v___x_1304_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
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
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1301_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1301_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object* v_lhs_u2080_1436_, lean_object* v_rhs_u2080_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_lhs_u2080_1436_, v_rhs_u2080_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_a_1438_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object* v_cls_1450_, lean_object* v_msg_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1450_, v_msg_1451_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object* v_cls_1464_, lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_1464_, v_msg_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v___y_1466_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object* v_lhs_1478_, lean_object* v_rhs_1479_, uint8_t v_abstract_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1478_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1479_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc(v___y_1481_);
v___x_1496_ = lean_grind_process_to_do(v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; 
lean_dec_ref_known(v___x_1496_, 1);
v___x_1497_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1493_, v_a_1495_, v___y_1481_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1526_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1526_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1526_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
if (v___x_1502_ == 0)
{
if (v_abstract_1480_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v_a_1495_);
lean_dec(v_a_1493_);
v___x_1503_ = lean_box(0);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1503_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
else
{
lean_object* v___x_1507_; 
lean_del_object(v___x_1500_);
v___x_1507_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_a_1493_, v_a_1495_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1507_;
}
}
else
{
lean_object* v___x_1508_; 
lean_del_object(v___x_1500_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc(v___y_1481_);
v___x_1508_ = lean_grind_mk_eq_proof(v_a_1493_, v_a_1495_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_a_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1513_);
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1508_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1508_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1495_);
lean_dec(v_a_1493_);
v_a_1527_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1497_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1497_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_a_1495_);
lean_dec(v_a_1493_);
v_a_1535_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1496_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1496_);
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
lean_dec(v_a_1493_);
v_a_1543_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1494_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1494_);
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
lean_dec_ref(v_rhs_1479_);
v_a_1551_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1492_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1492_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object* v_lhs_1559_, lean_object* v_rhs_1560_, lean_object* v_abstract_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v_abstract_boxed_1573_; lean_object* v_res_1574_; 
v_abstract_boxed_1573_ = lean_unbox(v_abstract_1561_);
v_res_1574_ = l_Lean_Meta_Grind_proveEq_x3f___lam__0(v_lhs_1559_, v_rhs_1560_, v_abstract_boxed_1573_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Meta_Grind_proveEq_x3f___closed__0));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object* v_lhs_1578_, lean_object* v_rhs_1579_, uint8_t v_abstract_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_toCold_1592_; lean_object* v_options_1593_; lean_object* v_inheritedTraceOptions_1594_; uint8_t v_hasTrace_1595_; lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; 
v_toCold_1592_ = lean_ctor_get(v_a_1589_, 0);
v_options_1593_ = lean_ctor_get(v_toCold_1592_, 2);
v_inheritedTraceOptions_1594_ = lean_ctor_get(v_toCold_1592_, 11);
v_hasTrace_1595_ = lean_ctor_get_uint8(v_options_1593_, sizeof(void*)*1);
v___x_1596_ = lean_box(v_abstract_1580_);
lean_inc_ref(v_rhs_1579_);
lean_inc_ref(v_lhs_1578_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed), 14, 3);
lean_closure_set(v___f_1597_, 0, v_lhs_1578_);
lean_closure_set(v___f_1597_, 1, v_rhs_1579_);
lean_closure_set(v___f_1597_, 2, v___x_1596_);
if (v_hasTrace_1595_ == 0)
{
v___y_1661_ = v_a_1581_;
v___y_1662_ = v_a_1582_;
v___y_1663_ = v_a_1583_;
v___y_1664_ = v_a_1584_;
v___y_1665_ = v_a_1585_;
v___y_1666_ = v_a_1586_;
v___y_1667_ = v_a_1587_;
v___y_1668_ = v_a_1588_;
v___y_1669_ = v_a_1589_;
v___y_1670_ = v_a_1590_;
goto v___jp_1660_;
}
else
{
lean_object* v_cls_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v_cls_1694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1696_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1594_, v_options_1593_, v___x_1695_);
if (v___x_1696_ == 0)
{
v___y_1661_ = v_a_1581_;
v___y_1662_ = v_a_1582_;
v___y_1663_ = v_a_1583_;
v___y_1664_ = v_a_1584_;
v___y_1665_ = v_a_1585_;
v___y_1666_ = v_a_1586_;
v___y_1667_ = v_a_1587_;
v___y_1668_ = v_a_1588_;
v___y_1669_ = v_a_1589_;
v___y_1670_ = v_a_1590_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1697_ = lean_obj_once(&l_Lean_Meta_Grind_proveEq_x3f___closed__1, &l_Lean_Meta_Grind_proveEq_x3f___closed__1_once, _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1);
lean_inc_ref(v_lhs_1578_);
v___x_1698_ = l_Lean_MessageData_ofExpr(v_lhs_1578_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
lean_inc_ref(v_rhs_1579_);
v___x_1702_ = l_Lean_MessageData_ofExpr(v_rhs_1579_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1694_, v___x_1705_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_dec_ref_known(v___x_1706_, 1);
v___y_1661_ = v_a_1581_;
v___y_1662_ = v_a_1582_;
v___y_1663_ = v_a_1583_;
v___y_1664_ = v_a_1584_;
v___y_1665_ = v_a_1585_;
v___y_1666_ = v_a_1586_;
v___y_1667_ = v_a_1587_;
v___y_1668_ = v_a_1588_;
v___y_1669_ = v_a_1589_;
v___y_1670_ = v_a_1590_;
goto v___jp_1660_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref(v___f_1597_);
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
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
v___jp_1598_:
{
if (lean_obj_tag(v___y_1609_) == 0)
{
lean_object* v_a_1610_; uint8_t v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___y_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___y_1609_, 1);
v___x_1611_ = lean_unbox(v_a_1610_);
lean_dec(v_a_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v___x_1612_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1597_, v___y_1608_, v___y_1603_, v___y_1606_, v___y_1607_, v___y_1599_, v___y_1602_, v___y_1600_, v___y_1604_, v___y_1601_, v___y_1605_);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; 
lean_dec_ref(v___f_1597_);
v___x_1613_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1578_, v_rhs_1579_, v___y_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1643_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1643_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1643_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_unbox(v_a_1614_);
lean_dec(v_a_1614_);
if (v___x_1618_ == 0)
{
if (v_abstract_1580_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v___x_1619_ = lean_box(0);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1619_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1616_);
v___x_1623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 13, 2);
lean_closure_set(v___x_1623_, 0, v_lhs_1578_);
lean_closure_set(v___x_1623_, 1, v_rhs_1579_);
v___x_1624_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___x_1623_, v___y_1608_, v___y_1603_, v___y_1606_, v___y_1607_, v___y_1599_, v___y_1602_, v___y_1600_, v___y_1604_, v___y_1601_, v___y_1605_);
return v___x_1624_;
}
}
else
{
lean_object* v___x_1625_; 
lean_del_object(v___x_1616_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1607_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1603_);
lean_inc(v___y_1608_);
v___x_1625_ = lean_grind_mk_eq_proof(v_lhs_1578_, v_rhs_1579_, v___y_1608_, v___y_1603_, v___y_1606_, v___y_1607_, v___y_1599_, v___y_1602_, v___y_1600_, v___y_1604_, v___y_1601_, v___y_1605_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1634_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_a_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1625_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1625_);
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
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v_a_1644_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1613_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1613_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___f_1597_);
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v_a_1652_ = lean_ctor_get(v___y_1609_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___y_1609_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___y_1609_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___y_1609_);
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
v___jp_1660_:
{
lean_object* v___x_1671_; 
lean_inc_ref(v_rhs_1579_);
lean_inc_ref(v_lhs_1578_);
v___x_1671_ = l_Lean_Meta_Grind_hasSameType(v_lhs_1578_, v_rhs_1579_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1685_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1685_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1685_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_unbox(v_a_1672_);
lean_dec(v_a_1672_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec_ref(v___f_1597_);
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v___x_1677_ = lean_box(0);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v___x_1681_; 
lean_del_object(v___x_1674_);
v___x_1681_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1578_, v___y_1661_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; uint8_t v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v___x_1683_ = lean_unbox(v_a_1682_);
if (v___x_1683_ == 0)
{
v___y_1599_ = v___y_1665_;
v___y_1600_ = v___y_1667_;
v___y_1601_ = v___y_1669_;
v___y_1602_ = v___y_1666_;
v___y_1603_ = v___y_1662_;
v___y_1604_ = v___y_1668_;
v___y_1605_ = v___y_1670_;
v___y_1606_ = v___y_1663_;
v___y_1607_ = v___y_1664_;
v___y_1608_ = v___y_1661_;
v___y_1609_ = v___x_1681_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1684_; 
lean_dec_ref_known(v___x_1681_, 1);
v___x_1684_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1579_, v___y_1661_);
v___y_1599_ = v___y_1665_;
v___y_1600_ = v___y_1667_;
v___y_1601_ = v___y_1669_;
v___y_1602_ = v___y_1666_;
v___y_1603_ = v___y_1662_;
v___y_1604_ = v___y_1668_;
v___y_1605_ = v___y_1670_;
v___y_1606_ = v___y_1663_;
v___y_1607_ = v___y_1664_;
v___y_1608_ = v___y_1661_;
v___y_1609_ = v___x_1684_;
goto v___jp_1598_;
}
}
else
{
v___y_1599_ = v___y_1665_;
v___y_1600_ = v___y_1667_;
v___y_1601_ = v___y_1669_;
v___y_1602_ = v___y_1666_;
v___y_1603_ = v___y_1662_;
v___y_1604_ = v___y_1668_;
v___y_1605_ = v___y_1670_;
v___y_1606_ = v___y_1663_;
v___y_1607_ = v___y_1664_;
v___y_1608_ = v___y_1661_;
v___y_1609_ = v___x_1681_;
goto v___jp_1598_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v___f_1597_);
lean_dec_ref(v_rhs_1579_);
lean_dec_ref(v_lhs_1578_);
v_a_1686_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1671_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1671_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object* v_lhs_1715_, lean_object* v_rhs_1716_, lean_object* v_abstract_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
uint8_t v_abstract_boxed_1729_; lean_object* v_res_1730_; 
v_abstract_boxed_1729_ = lean_unbox(v_abstract_1717_);
v_res_1730_ = l_Lean_Meta_Grind_proveEq_x3f(v_lhs_1715_, v_rhs_1716_, v_abstract_boxed_1729_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec(v_a_1718_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object* v_lhs_1731_, lean_object* v_rhs_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1731_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc(v___y_1733_);
v___x_1748_ = lean_grind_process_to_do(v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
lean_dec_ref_known(v___x_1748_, 1);
v___x_1749_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1745_, v_a_1747_, v___y_1733_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1777_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1777_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1777_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_unbox(v_a_1750_);
lean_dec(v_a_1750_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec(v_a_1747_);
lean_dec(v_a_1745_);
v___x_1755_ = lean_box(0);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_object* v___x_1759_; 
lean_del_object(v___x_1752_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc(v___y_1733_);
v___x_1759_ = lean_grind_mk_heq_proof(v_a_1745_, v_a_1747_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
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
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1759_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1759_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1747_);
lean_dec(v_a_1745_);
v_a_1778_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1749_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1749_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_a_1747_);
lean_dec(v_a_1745_);
v_a_1786_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1748_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1748_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1745_);
v_a_1794_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1746_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1746_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref(v_rhs_1732_);
v_a_1802_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1744_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1744_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object* v_lhs_1810_, lean_object* v_rhs_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(v_lhs_1810_, v_rhs_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object* v_lhs_1824_, lean_object* v_rhs_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___f_1837_; lean_object* v___y_1839_; lean_object* v___x_1888_; 
lean_inc_ref(v_rhs_1825_);
lean_inc_ref(v_lhs_1824_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1837_, 0, v_lhs_1824_);
lean_closure_set(v___f_1837_, 1, v_rhs_1825_);
v___x_1888_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1824_, v_a_1826_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; uint8_t v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v___x_1890_ = lean_unbox(v_a_1889_);
if (v___x_1890_ == 0)
{
v___y_1839_ = v___x_1888_;
goto v___jp_1838_;
}
else
{
lean_object* v___x_1891_; 
lean_dec_ref_known(v___x_1888_, 1);
v___x_1891_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1825_, v_a_1826_);
v___y_1839_ = v___x_1891_;
goto v___jp_1838_;
}
}
else
{
v___y_1839_ = v___x_1888_;
goto v___jp_1838_;
}
v___jp_1838_:
{
if (lean_obj_tag(v___y_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___y_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___y_1839_, 1);
v___x_1841_ = lean_unbox(v_a_1840_);
lean_dec(v_a_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
v___x_1842_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1837_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; 
lean_dec_ref(v___f_1837_);
v___x_1843_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1824_, v_rhs_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1871_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1871_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1871_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_unbox(v_a_1844_);
lean_dec(v_a_1844_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
v___x_1849_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1849_);
v___x_1851_ = v___x_1846_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v___x_1853_; 
lean_del_object(v___x_1846_);
lean_inc(v_a_1835_);
lean_inc_ref(v_a_1834_);
lean_inc(v_a_1833_);
lean_inc_ref(v_a_1832_);
lean_inc(v_a_1831_);
lean_inc_ref(v_a_1830_);
lean_inc(v_a_1829_);
lean_inc_ref(v_a_1828_);
lean_inc(v_a_1827_);
lean_inc(v_a_1826_);
v___x_1853_ = lean_grind_mk_heq_proof(v_lhs_1824_, v_rhs_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1862_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
v_a_1863_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1853_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1853_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
v_a_1872_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1843_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1843_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v___f_1837_);
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
v_a_1880_ = lean_ctor_get(v___y_1839_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___y_1839_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___y_1839_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___y_1839_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object* v_lhs_1892_, lean_object* v_rhs_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Grind_proveHEq_x3f(v_lhs_1892_, v_rhs_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec(v_a_1894_);
return v_res_1905_;
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
