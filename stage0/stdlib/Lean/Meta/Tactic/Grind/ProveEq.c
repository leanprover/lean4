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
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
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
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_31_, v___y_39_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v___y_40_ = stack[9].m_obj;
lean_object* v___y_41_ = stack[10].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(lean_object* v_e_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(v_e_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec(v___y_46_);
return v_res_57_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(lean_object* v_e_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_58_, v_a_59_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_102_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_102_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_102_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_102_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = lean_unbox(v_a_71_);
lean_dec(v_a_71_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v_a_77_; lean_object* v___x_78_; 
lean_del_object(v___x_73_);
v___x_76_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_58_, v_a_66_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref(v___x_76_);
v___x_78_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_77_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc_n(v_a_79_, 2);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_box(0);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
lean_inc(v_a_60_);
lean_inc(v_a_59_);
v___x_82_ = lean_grind_internalize(v_a_79_, v___x_80_, v___x_81_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_82_, 0);
lean_dec(v_unused_90_);
v___x_84_ = v___x_82_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_dec(v___x_82_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v_a_79_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_79_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v_a_79_);
v_a_91_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_82_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_82_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
else
{
return v___x_78_;
}
}
else
{
lean_object* v___x_100_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v_e_58_);
v___x_100_ = v___x_73_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_e_58_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v_e_58_);
v_a_103_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_70_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_70_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_58_ = stack[0].m_obj;
lean_object* v_a_59_ = stack[1].m_obj;
lean_object* v_a_60_ = stack[2].m_obj;
lean_object* v_a_61_ = stack[3].m_obj;
lean_object* v_a_62_ = stack[4].m_obj;
lean_object* v_a_63_ = stack[5].m_obj;
lean_object* v_a_64_ = stack[6].m_obj;
lean_object* v_a_65_ = stack[7].m_obj;
lean_object* v_a_66_ = stack[8].m_obj;
lean_object* v_a_67_ = stack[9].m_obj;
lean_object* v_a_68_ = stack[10].m_obj;
lean_object* v_res_111_;
v_res_111_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_e_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(lean_object* v_e_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_e_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec(v_a_113_);
return v_res_124_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_dec_lt(v___x_128_, v_a_125_);
v___x_130_ = lean_box(v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_126_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_125_ = stack[0].m_obj;
lean_object* v_a_126_ = stack[1].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_125_, v_a_126_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_135_, v_a_136_);
lean_dec(v_a_135_);
return v_res_138_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_139_, v_a_140_);
return v___x_152_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_139_ = stack[0].m_obj;
lean_object* v_a_140_ = stack[1].m_obj;
lean_object* v_a_141_ = stack[2].m_obj;
lean_object* v_a_142_ = stack[3].m_obj;
lean_object* v_a_143_ = stack[4].m_obj;
lean_object* v_a_144_ = stack[5].m_obj;
lean_object* v_a_145_ = stack[6].m_obj;
lean_object* v_a_146_ = stack[7].m_obj;
lean_object* v_a_147_ = stack[8].m_obj;
lean_object* v_a_148_ = stack[9].m_obj;
lean_object* v_a_149_ = stack[10].m_obj;
lean_object* v_a_150_ = stack[11].m_obj;
lean_object* v_res_153_;
v_res_153_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec(v_a_156_);
lean_dec(v_a_154_);
return v_res_167_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_a_169_, v___x_182_);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
lean_inc(v_a_171_);
v___x_184_ = lean_apply_13(v_x_168_, v___x_183_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, lean_box(0));
return v___x_184_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_168_ = stack[0].m_obj;
lean_object* v_a_169_ = stack[1].m_obj;
lean_object* v_a_170_ = stack[2].m_obj;
lean_object* v_a_171_ = stack[3].m_obj;
lean_object* v_a_172_ = stack[4].m_obj;
lean_object* v_a_173_ = stack[5].m_obj;
lean_object* v_a_174_ = stack[6].m_obj;
lean_object* v_a_175_ = stack[7].m_obj;
lean_object* v_a_176_ = stack[8].m_obj;
lean_object* v_a_177_ = stack[9].m_obj;
lean_object* v_a_178_ = stack[10].m_obj;
lean_object* v_a_179_ = stack[11].m_obj;
lean_object* v_a_180_ = stack[12].m_obj;
lean_object* v_res_185_;
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(v_x_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(lean_object* v_x_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(v_x_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec(v_a_189_);
lean_dec(v_a_187_);
return v_res_200_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_object* v_00_u03b1_201_, lean_object* v_x_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_a_203_, v___x_216_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc(v_a_205_);
v___x_218_ = lean_apply_13(v_x_202_, v___x_217_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_202_ = stack[1].m_obj;
lean_object* v_a_203_ = stack[2].m_obj;
lean_object* v_a_204_ = stack[3].m_obj;
lean_object* v_a_205_ = stack[4].m_obj;
lean_object* v_a_206_ = stack[5].m_obj;
lean_object* v_a_207_ = stack[6].m_obj;
lean_object* v_a_208_ = stack[7].m_obj;
lean_object* v_a_209_ = stack[8].m_obj;
lean_object* v_a_210_ = stack[9].m_obj;
lean_object* v_a_211_ = stack[10].m_obj;
lean_object* v_a_212_ = stack[11].m_obj;
lean_object* v_a_213_ = stack[12].m_obj;
lean_object* v_a_214_ = stack[13].m_obj;
lean_object* v_res_219_;
v_res_219_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(lean_box(0), v_x_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(lean_object* v_00_u03b1_220_, lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(v_00_u03b1_220_, v_x_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec(v_a_224_);
lean_dec(v_a_222_);
return v_res_235_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2(void){
_start:
{
lean_object* v_i_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_i_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1));
v___x_241_ = lean_name_append_index_after(v___x_240_, v_i_239_);
return v___x_241_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(lean_object* v_as_242_, size_t v_sz_243_, size_t v_i_244_, lean_object* v_b_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_usize_dec_lt(v_i_244_, v_sz_243_);
if (v___x_246_ == 0)
{
return v_b_245_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; size_t v___x_251_; size_t v___x_252_; 
v_a_247_ = lean_array_uget_borrowed(v_as_242_, v_i_244_);
v___x_248_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2);
v___x_249_ = 0;
lean_inc(v_a_247_);
v___x_250_ = l_Lean_mkLambda(v___x_248_, v___x_249_, v_a_247_, v_b_245_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_244_, v___x_251_);
v_i_244_ = v___x_252_;
v_b_245_ = v___x_250_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_242_ = stack[0].m_obj;
size_t v_sz_243_ = stack[1].m_num;
size_t v_i_244_ = stack[2].m_num;
lean_object* v_b_245_ = stack[3].m_obj;
lean_object* v_res_254_;
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_as_242_, v_sz_243_, v_i_244_, v_b_245_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(lean_object* v_as_255_, lean_object* v_sz_256_, lean_object* v_i_257_, lean_object* v_b_258_){
_start:
{
size_t v_sz_boxed_259_; size_t v_i_boxed_260_; lean_object* v_res_261_; 
v_sz_boxed_259_ = lean_unbox_usize(v_sz_256_);
lean_dec(v_sz_256_);
v_i_boxed_260_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_as_255_, v_sz_boxed_259_, v_i_boxed_260_, v_b_258_);
lean_dec_ref(v_as_255_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(lean_object* v_varTypes_262_, lean_object* v_b_263_){
_start:
{
size_t v_sz_264_; size_t v___x_265_; lean_object* v___x_266_; 
v_sz_264_ = lean_array_size(v_varTypes_262_);
v___x_265_ = ((size_t)0ULL);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_varTypes_262_, v_sz_264_, v___x_265_, v_b_263_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(lean_object* v_varTypes_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_267_, v_b_268_);
lean_dec_ref(v_varTypes_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(lean_object* v_a_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
else
{
lean_object* v_key_273_; lean_object* v_value_274_; lean_object* v_tail_275_; uint8_t v___y_277_; lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; uint8_t v___x_284_; 
v_key_273_ = lean_ctor_get(v_x_271_, 0);
v_value_274_ = lean_ctor_get(v_x_271_, 1);
v_tail_275_ = lean_ctor_get(v_x_271_, 2);
v_fst_280_ = lean_ctor_get(v_key_273_, 0);
v_snd_281_ = lean_ctor_get(v_key_273_, 1);
v_fst_282_ = lean_ctor_get(v_a_270_, 0);
v_snd_283_ = lean_ctor_get(v_a_270_, 1);
v___x_284_ = lean_expr_eqv(v_fst_280_, v_fst_282_);
if (v___x_284_ == 0)
{
v___y_277_ = v___x_284_;
goto v___jp_276_;
}
else
{
uint8_t v___x_285_; 
v___x_285_ = lean_expr_eqv(v_snd_281_, v_snd_283_);
v___y_277_ = v___x_285_;
goto v___jp_276_;
}
v___jp_276_:
{
if (v___y_277_ == 0)
{
v_x_271_ = v_tail_275_;
goto _start;
}
else
{
lean_object* v___x_279_; 
lean_inc(v_value_274_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_value_274_);
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_286_, v_x_287_);
lean_dec(v_x_287_);
lean_dec_ref(v_a_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(lean_object* v_m_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_buckets_291_; lean_object* v_fst_292_; lean_object* v_snd_293_; lean_object* v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v_fold_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_buckets_291_ = lean_ctor_get(v_m_289_, 1);
v_fst_292_ = lean_ctor_get(v_a_290_, 0);
v_snd_293_ = lean_ctor_get(v_a_290_, 1);
v___x_294_ = lean_array_get_size(v_buckets_291_);
v___x_295_ = l_Lean_Expr_hash(v_fst_292_);
v___x_296_ = l_Lean_Expr_hash(v_snd_293_);
v___x_297_ = lean_uint64_mix_hash(v___x_295_, v___x_296_);
v___x_298_ = 32ULL;
v___x_299_ = lean_uint64_shift_right(v___x_297_, v___x_298_);
v_fold_300_ = lean_uint64_xor(v___x_297_, v___x_299_);
v___x_301_ = 16ULL;
v___x_302_ = lean_uint64_shift_right(v_fold_300_, v___x_301_);
v___x_303_ = lean_uint64_xor(v_fold_300_, v___x_302_);
v___x_304_ = lean_uint64_to_usize(v___x_303_);
v___x_305_ = lean_usize_of_nat(v___x_294_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v___x_305_, v___x_306_);
v___x_308_ = lean_usize_land(v___x_304_, v___x_307_);
v___x_309_ = lean_array_uget_borrowed(v_buckets_291_, v___x_308_);
v___x_310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_290_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(lean_object* v_m_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_311_, v_a_312_);
lean_dec_ref(v_a_312_);
lean_dec_ref(v_m_311_);
return v_res_313_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(lean_object* v_a_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
else
{
lean_object* v_key_317_; lean_object* v_tail_318_; uint8_t v___y_320_; lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v_fst_324_; lean_object* v_snd_325_; uint8_t v___x_326_; 
v_key_317_ = lean_ctor_get(v_x_315_, 0);
v_tail_318_ = lean_ctor_get(v_x_315_, 2);
v_fst_322_ = lean_ctor_get(v_key_317_, 0);
v_snd_323_ = lean_ctor_get(v_key_317_, 1);
v_fst_324_ = lean_ctor_get(v_a_314_, 0);
v_snd_325_ = lean_ctor_get(v_a_314_, 1);
v___x_326_ = lean_expr_eqv(v_fst_322_, v_fst_324_);
if (v___x_326_ == 0)
{
v___y_320_ = v___x_326_;
goto v___jp_319_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = lean_expr_eqv(v_snd_323_, v_snd_325_);
v___y_320_ = v___x_327_;
goto v___jp_319_;
}
v___jp_319_:
{
if (v___y_320_ == 0)
{
v_x_315_ = v_tail_318_;
goto _start;
}
else
{
return v___y_320_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_314_ = stack[0].m_obj;
lean_object* v_x_315_ = stack[1].m_obj;
uint8_t v_res_328_;
v_res_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_314_, v_x_315_);
stack->m_num = v_res_328_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec_ref(v_a_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(lean_object* v_a_333_, lean_object* v_b_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_dec(v_b_334_);
lean_dec_ref(v_a_333_);
return v_x_335_;
}
else
{
lean_object* v_key_336_; lean_object* v_value_337_; lean_object* v_tail_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_357_; 
v_key_336_ = lean_ctor_get(v_x_335_, 0);
v_value_337_ = lean_ctor_get(v_x_335_, 1);
v_tail_338_ = lean_ctor_get(v_x_335_, 2);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_357_ == 0)
{
v___x_340_ = v_x_335_;
v_isShared_341_ = v_isSharedCheck_357_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_tail_338_);
lean_inc(v_value_337_);
lean_inc(v_key_336_);
lean_dec(v_x_335_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_357_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint8_t v___y_343_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v_fst_353_; lean_object* v_snd_354_; uint8_t v___x_355_; 
v_fst_351_ = lean_ctor_get(v_key_336_, 0);
v_snd_352_ = lean_ctor_get(v_key_336_, 1);
v_fst_353_ = lean_ctor_get(v_a_333_, 0);
v_snd_354_ = lean_ctor_get(v_a_333_, 1);
v___x_355_ = lean_expr_eqv(v_fst_351_, v_fst_353_);
if (v___x_355_ == 0)
{
v___y_343_ = v___x_355_;
goto v___jp_342_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = lean_expr_eqv(v_snd_352_, v_snd_354_);
v___y_343_ = v___x_356_;
goto v___jp_342_;
}
v___jp_342_:
{
if (v___y_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_333_, v_b_334_, v_tail_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 2, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_key_336_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_value_337_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v_value_337_);
lean_dec(v_key_336_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_b_334_);
lean_ctor_set(v___x_340_, 0, v_a_333_);
v___x_349_ = v___x_340_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_333_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_b_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_tail_338_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
return v_x_358_;
}
else
{
lean_object* v_key_360_; lean_object* v_value_361_; lean_object* v_tail_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_389_; 
v_key_360_ = lean_ctor_get(v_x_359_, 0);
v_value_361_ = lean_ctor_get(v_x_359_, 1);
v_tail_362_ = lean_ctor_get(v_x_359_, 2);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_359_);
if (v_isSharedCheck_389_ == 0)
{
v___x_364_ = v_x_359_;
v_isShared_365_ = v_isSharedCheck_389_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_tail_362_);
lean_inc(v_value_361_);
lean_inc(v_key_360_);
lean_dec(v_x_359_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_389_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v_fold_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v_fst_366_ = lean_ctor_get(v_key_360_, 0);
v_snd_367_ = lean_ctor_get(v_key_360_, 1);
v___x_368_ = lean_array_get_size(v_x_358_);
v___x_369_ = l_Lean_Expr_hash(v_fst_366_);
v___x_370_ = l_Lean_Expr_hash(v_snd_367_);
v___x_371_ = lean_uint64_mix_hash(v___x_369_, v___x_370_);
v___x_372_ = 32ULL;
v___x_373_ = lean_uint64_shift_right(v___x_371_, v___x_372_);
v_fold_374_ = lean_uint64_xor(v___x_371_, v___x_373_);
v___x_375_ = 16ULL;
v___x_376_ = lean_uint64_shift_right(v_fold_374_, v___x_375_);
v___x_377_ = lean_uint64_xor(v_fold_374_, v___x_376_);
v___x_378_ = lean_uint64_to_usize(v___x_377_);
v___x_379_ = lean_usize_of_nat(v___x_368_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v___x_379_, v___x_380_);
v___x_382_ = lean_usize_land(v___x_378_, v___x_381_);
v___x_383_ = lean_array_uget_borrowed(v_x_358_, v___x_382_);
lean_inc(v___x_383_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v___x_383_);
v___x_385_ = v___x_364_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_key_360_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_value_361_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v___x_383_);
v___x_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_array_uset(v_x_358_, v___x_382_, v___x_385_);
v_x_358_ = v___x_386_;
v_x_359_ = v_tail_362_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(lean_object* v_i_390_, lean_object* v_source_391_, lean_object* v_target_392_){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_array_get_size(v_source_391_);
v___x_394_ = lean_nat_dec_lt(v_i_390_, v___x_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v_source_391_);
lean_dec(v_i_390_);
return v_target_392_;
}
else
{
lean_object* v_es_395_; lean_object* v___x_396_; lean_object* v_source_397_; lean_object* v_target_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_es_395_ = lean_array_fget(v_source_391_, v_i_390_);
v___x_396_ = lean_box(0);
v_source_397_ = lean_array_fset(v_source_391_, v_i_390_, v___x_396_);
v_target_398_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_target_392_, v_es_395_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_add(v_i_390_, v___x_399_);
lean_dec(v_i_390_);
v_i_390_ = v___x_400_;
v_source_391_ = v_source_397_;
v_target_392_ = v_target_398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(lean_object* v_data_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_nbuckets_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_403_ = lean_array_get_size(v_data_402_);
v___x_404_ = lean_unsigned_to_nat(2u);
v_nbuckets_405_ = lean_nat_mul(v___x_403_, v___x_404_);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_box(0);
v___x_408_ = lean_mk_array(v_nbuckets_405_, v___x_407_);
v___x_409_ = lean_array_propagate_mark(v_data_402_, v___x_408_);
v___x_410_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v___x_406_, v_data_402_, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(lean_object* v_m_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v_size_414_; lean_object* v_buckets_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_462_; 
v_size_414_ = lean_ctor_get(v_m_411_, 0);
v_buckets_415_ = lean_ctor_get(v_m_411_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_m_411_);
if (v_isSharedCheck_462_ == 0)
{
v___x_417_ = v_m_411_;
v_isShared_418_ = v_isSharedCheck_462_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_buckets_415_);
lean_inc(v_size_414_);
lean_dec(v_m_411_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_462_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_bkt_436_; uint8_t v___x_437_; 
v_fst_419_ = lean_ctor_get(v_a_412_, 0);
v_snd_420_ = lean_ctor_get(v_a_412_, 1);
v___x_421_ = lean_array_get_size(v_buckets_415_);
v___x_422_ = l_Lean_Expr_hash(v_fst_419_);
v___x_423_ = l_Lean_Expr_hash(v_snd_420_);
v___x_424_ = lean_uint64_mix_hash(v___x_422_, v___x_423_);
v___x_425_ = 32ULL;
v___x_426_ = lean_uint64_shift_right(v___x_424_, v___x_425_);
v_fold_427_ = lean_uint64_xor(v___x_424_, v___x_426_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_421_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v_bkt_436_ = lean_array_uget_borrowed(v_buckets_415_, v___x_435_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_412_, v_bkt_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v_size_x27_439_; lean_object* v___x_440_; lean_object* v_buckets_x27_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v_size_x27_439_ = lean_nat_add(v_size_414_, v___x_438_);
lean_dec(v_size_414_);
lean_inc(v_bkt_436_);
v___x_440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_440_, 0, v_a_412_);
lean_ctor_set(v___x_440_, 1, v_b_413_);
lean_ctor_set(v___x_440_, 2, v_bkt_436_);
v_buckets_x27_441_ = lean_array_uset(v_buckets_415_, v___x_435_, v___x_440_);
v___x_442_ = lean_unsigned_to_nat(4u);
v___x_443_ = lean_nat_mul(v_size_x27_439_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(3u);
v___x_445_ = lean_nat_div(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_array_get_size(v_buckets_x27_441_);
v___x_447_ = lean_nat_dec_le(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
if (v___x_447_ == 0)
{
lean_object* v_val_448_; lean_object* v___x_450_; 
v_val_448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_buckets_x27_441_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_val_448_);
lean_ctor_set(v___x_417_, 0, v_size_x27_439_);
v___x_450_ = v___x_417_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_size_x27_439_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_val_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
lean_object* v___x_453_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_buckets_x27_441_);
lean_ctor_set(v___x_417_, 0, v_size_x27_439_);
v___x_453_ = v___x_417_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_buckets_x27_441_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v___x_455_; lean_object* v_buckets_x27_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
lean_inc(v_bkt_436_);
v___x_455_ = lean_box(0);
v_buckets_x27_456_ = lean_array_uset(v_buckets_415_, v___x_435_, v___x_455_);
v___x_457_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_412_, v_b_413_, v_bkt_436_);
v___x_458_ = lean_array_uset(v_buckets_x27_456_, v___x_435_, v___x_457_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_458_);
v___x_460_ = v___x_417_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_size_414_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(lean_object* v_lhs_463_, lean_object* v_rhs_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___x_759_; 
v___x_759_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_875_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_875_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_875_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_875_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
if (lean_obj_tag(v_a_760_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v___x_764_ = lean_box(0);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v_val_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_874_; 
lean_del_object(v___x_762_);
v_val_768_ = lean_ctor_get(v_a_760_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_a_760_);
if (v_isSharedCheck_874_ == 0)
{
v___x_770_ = v_a_760_;
v_isShared_771_ = v_isSharedCheck_874_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_val_768_);
lean_dec(v_a_760_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_874_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_fst_772_; uint8_t v___x_773_; 
v_fst_772_ = lean_ctor_get(v_val_768_, 0);
v___x_773_ = lean_unbox(v_fst_772_);
if (v___x_773_ == 0)
{
lean_object* v_snd_774_; 
lean_del_object(v___x_770_);
v_snd_774_ = lean_ctor_get(v_val_768_, 1);
lean_inc(v_snd_774_);
lean_dec(v_val_768_);
v___y_527_ = v_a_465_;
v___y_528_ = v_snd_774_;
v___y_529_ = v_a_467_;
v___y_530_ = v_a_468_;
v___y_531_ = v_a_469_;
v___y_532_ = v_a_470_;
v___y_533_ = v_a_471_;
v___y_534_ = v_a_472_;
v___y_535_ = v_a_473_;
v___y_536_ = v_a_474_;
v___y_537_ = v_a_475_;
v___y_538_ = v_a_476_;
goto v___jp_526_;
}
else
{
lean_object* v_snd_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_872_; 
v_snd_775_ = lean_ctor_get(v_val_768_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_val_768_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_val_768_, 0);
lean_dec(v_unused_873_);
v___x_777_ = v_val_768_;
v_isShared_778_ = v_isSharedCheck_872_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snd_775_);
lean_dec(v_val_768_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_872_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
uint8_t v___x_779_; 
v___x_779_ = l_Lean_Expr_hasLooseBVars(v_lhs_463_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = l_Lean_Expr_hasLooseBVars(v_rhs_464_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_inc_ref(v_lhs_463_);
v___x_781_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_463_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
lean_inc_ref(v_rhs_464_);
v___x_783_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_464_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
lean_inc(v_a_476_);
lean_inc_ref(v_a_475_);
lean_inc(v_a_474_);
lean_inc_ref(v_a_473_);
lean_inc(v_a_472_);
lean_inc_ref(v_a_471_);
lean_inc(v_a_470_);
lean_inc_ref(v_a_469_);
lean_inc(v_a_468_);
lean_inc(v_a_467_);
v___x_785_ = lean_grind_process_to_do(v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; 
lean_dec_ref_known(v___x_785_, 1);
v___x_786_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_782_, v_a_784_, v_a_467_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; uint8_t v___x_788_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = lean_unbox(v_a_787_);
lean_dec(v_a_787_);
if (v___x_788_ == 0)
{
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
v___y_527_ = v_a_465_;
v___y_528_ = v_snd_775_;
v___y_529_ = v_a_467_;
v___y_530_ = v_a_468_;
v___y_531_ = v_a_469_;
v___y_532_ = v_a_470_;
v___y_533_ = v_a_471_;
v___y_534_ = v_a_472_;
v___y_535_ = v_a_473_;
v___y_536_ = v_a_474_;
v___y_537_ = v_a_475_;
v___y_538_ = v_a_476_;
goto v___jp_526_;
}
else
{
lean_object* v___x_789_; 
lean_inc(v_a_784_);
lean_inc(v_a_782_);
v___x_789_ = l_Lean_Meta_Grind_hasSameType(v_a_782_, v_a_784_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; uint8_t v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_unbox(v_a_790_);
lean_dec(v_a_790_);
if (v___x_791_ == 0)
{
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
v___y_527_ = v_a_465_;
v___y_528_ = v_snd_775_;
v___y_529_ = v_a_467_;
v___y_530_ = v_a_468_;
v___y_531_ = v_a_469_;
v___y_532_ = v_a_470_;
v___y_533_ = v_a_471_;
v___y_534_ = v_a_472_;
v___y_535_ = v_a_473_;
v___y_536_ = v_a_474_;
v___y_537_ = v_a_475_;
v___y_538_ = v_a_476_;
goto v___jp_526_;
}
else
{
lean_object* v___x_792_; 
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
lean_inc(v_a_476_);
lean_inc_ref(v_a_475_);
lean_inc(v_a_474_);
lean_inc_ref(v_a_473_);
lean_inc(v_a_782_);
v___x_792_ = lean_infer_type(v_a_782_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_823_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_823_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_823_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_823_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_cache_797_; lean_object* v_varTypes_798_; lean_object* v_lhss_799_; lean_object* v_rhss_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_822_; 
v_cache_797_ = lean_ctor_get(v_snd_775_, 0);
v_varTypes_798_ = lean_ctor_get(v_snd_775_, 1);
v_lhss_799_ = lean_ctor_get(v_snd_775_, 2);
v_rhss_800_ = lean_ctor_get(v_snd_775_, 3);
v_isSharedCheck_822_ = !lean_is_exclusive(v_snd_775_);
if (v_isSharedCheck_822_ == 0)
{
v___x_802_ = v_snd_775_;
v_isShared_803_ = v_isSharedCheck_822_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_rhss_800_);
lean_inc(v_lhss_799_);
lean_inc(v_varTypes_798_);
lean_inc(v_cache_797_);
lean_dec(v_snd_775_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_822_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_804_ = lean_array_get_size(v_varTypes_798_);
v___x_805_ = lean_nat_add(v___x_804_, v_a_465_);
v___x_806_ = lean_array_push(v_varTypes_798_, v_a_793_);
v___x_807_ = lean_array_push(v_lhss_799_, v_a_782_);
v___x_808_ = lean_array_push(v_rhss_800_, v_a_784_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 3, v___x_808_);
lean_ctor_set(v___x_802_, 2, v___x_807_);
lean_ctor_set(v___x_802_, 1, v___x_806_);
v___x_810_ = v___x_802_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_cache_797_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___x_808_);
v___x_810_ = v_reuseFailAlloc_821_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l_Lean_mkBVar(v___x_805_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_810_);
lean_ctor_set(v___x_777_, 0, v___x_811_);
v___x_813_ = v___x_777_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_810_);
v___x_813_ = v_reuseFailAlloc_820_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_813_);
v___x_815_ = v___x_770_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_815_);
v___x_817_ = v___x_795_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_dec(v_snd_775_);
lean_del_object(v___x_770_);
v_a_824_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_792_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_792_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_dec(v_snd_775_);
lean_del_object(v___x_770_);
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v_a_832_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_789_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_789_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_dec(v_snd_775_);
lean_del_object(v___x_770_);
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v_a_840_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_786_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_786_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_dec(v_snd_775_);
lean_del_object(v___x_770_);
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v_a_848_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_785_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_785_);
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
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_782_);
lean_del_object(v___x_777_);
lean_dec(v_snd_775_);
lean_del_object(v___x_770_);
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v_a_856_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_783_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_783_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_777_);
lean_dec(v_snd_775_);
lean_del_object(v___x_770_);
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v_a_864_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_781_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_781_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
v___y_527_ = v_a_465_;
v___y_528_ = v_snd_775_;
v___y_529_ = v_a_467_;
v___y_530_ = v_a_468_;
v___y_531_ = v_a_469_;
v___y_532_ = v_a_470_;
v___y_533_ = v_a_471_;
v___y_534_ = v_a_472_;
v___y_535_ = v_a_473_;
v___y_536_ = v_a_474_;
v___y_537_ = v_a_475_;
v___y_538_ = v_a_476_;
goto v___jp_526_;
}
}
else
{
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
v___y_527_ = v_a_465_;
v___y_528_ = v_snd_775_;
v___y_529_ = v_a_467_;
v___y_530_ = v_a_468_;
v___y_531_ = v_a_469_;
v___y_532_ = v_a_470_;
v___y_533_ = v_a_471_;
v___y_534_ = v_a_472_;
v___y_535_ = v_a_473_;
v___y_536_ = v_a_474_;
v___y_537_ = v_a_475_;
v___y_538_ = v_a_476_;
goto v___jp_526_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v_a_876_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_759_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_759_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
v___jp_478_:
{
if (v___y_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref(v___y_494_);
lean_dec(v___y_490_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v___y_481_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_494_, v___y_481_, v___y_485_, v___y_482_, v___y_483_, v___y_492_, v___y_479_, v___y_480_, v___y_486_, v___y_493_, v___y_488_, v___y_489_, v___y_491_, v___y_484_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
if (lean_obj_tag(v_a_499_) == 0)
{
lean_dec(v___y_490_);
lean_dec(v___y_487_);
return v___x_498_;
}
else
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_524_; 
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_525_);
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_524_;
goto v_resetjp_500_;
}
else
{
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_524_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_523_; 
v_val_503_ = lean_ctor_get(v_a_499_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_523_ == 0)
{
v___x_505_ = v_a_499_;
v_isShared_506_ = v_isSharedCheck_523_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v_a_499_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_523_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_522_; 
v_fst_507_ = lean_ctor_get(v_val_503_, 0);
v_snd_508_ = lean_ctor_get(v_val_503_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_val_503_);
if (v_isSharedCheck_522_ == 0)
{
v___x_510_ = v_val_503_;
v_isShared_511_ = v_isSharedCheck_522_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_inc(v_fst_507_);
lean_dec(v_val_503_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_522_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = l_Lean_Expr_proj___override(v___y_487_, v___y_490_, v_fst_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_508_);
v___x_514_ = v_reuseFailAlloc_521_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_514_);
v___x_516_ = v___x_505_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_516_);
v___x_518_ = v___x_501_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
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
lean_dec(v___y_490_);
lean_dec(v___y_487_);
return v___x_498_;
}
}
}
v___jp_526_:
{
switch(lean_obj_tag(v_lhs_463_))
{
case 5:
{
if (lean_obj_tag(v_rhs_464_) == 5)
{
lean_object* v_fn_539_; lean_object* v_arg_540_; lean_object* v_fn_541_; lean_object* v_arg_542_; lean_object* v___x_543_; 
v_fn_539_ = lean_ctor_get(v_lhs_463_, 0);
lean_inc_ref(v_fn_539_);
v_arg_540_ = lean_ctor_get(v_lhs_463_, 1);
lean_inc_ref(v_arg_540_);
lean_dec_ref_known(v_lhs_463_, 2);
v_fn_541_ = lean_ctor_get(v_rhs_464_, 0);
lean_inc_ref(v_fn_541_);
v_arg_542_ = lean_ctor_get(v_rhs_464_, 1);
lean_inc_ref(v_arg_542_);
lean_dec_ref_known(v_rhs_464_, 2);
v___x_543_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_fn_539_, v_fn_541_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
if (lean_obj_tag(v_a_544_) == 0)
{
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_540_);
return v___x_543_;
}
else
{
lean_object* v_val_545_; lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_548_; 
lean_inc_ref(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v_val_545_ = lean_ctor_get(v_a_544_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_a_544_, 1);
v_fst_546_ = lean_ctor_get(v_val_545_, 0);
lean_inc(v_fst_546_);
v_snd_547_ = lean_ctor_get(v_val_545_, 1);
lean_inc(v_snd_547_);
lean_dec(v_val_545_);
v___x_548_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_arg_540_, v_arg_542_, v___y_527_, v_snd_547_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
if (lean_obj_tag(v_a_549_) == 0)
{
lean_dec(v_fst_546_);
return v___x_548_;
}
else
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_574_; 
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v___x_548_, 0);
lean_dec(v_unused_575_);
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_574_;
goto v_resetjp_550_;
}
else
{
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_574_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_573_; 
v_val_553_ = lean_ctor_get(v_a_549_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_573_ == 0)
{
v___x_555_ = v_a_549_;
v_isShared_556_ = v_isSharedCheck_573_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_dec(v_a_549_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_573_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_572_; 
v_fst_557_ = lean_ctor_get(v_val_553_, 0);
v_snd_558_ = lean_ctor_get(v_val_553_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_val_553_);
if (v_isSharedCheck_572_ == 0)
{
v___x_560_ = v_val_553_;
v_isShared_561_ = v_isSharedCheck_572_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_snd_558_);
lean_inc(v_fst_557_);
lean_dec(v_val_553_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_572_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = l_Lean_Expr_app___override(v_fst_546_, v_fst_557_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_snd_558_);
v___x_564_ = v_reuseFailAlloc_571_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_564_);
v___x_566_ = v___x_555_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_566_);
v___x_568_ = v___x_551_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
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
lean_dec(v_fst_546_);
return v___x_548_;
}
}
}
else
{
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_540_);
return v___x_543_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref_known(v_lhs_463_, 2);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
case 6:
{
if (lean_obj_tag(v_rhs_464_) == 6)
{
lean_object* v_binderName_578_; lean_object* v_binderType_579_; lean_object* v_body_580_; uint8_t v_binderInfo_581_; lean_object* v_binderType_582_; lean_object* v_body_583_; lean_object* v___x_584_; 
v_binderName_578_ = lean_ctor_get(v_lhs_463_, 0);
lean_inc(v_binderName_578_);
v_binderType_579_ = lean_ctor_get(v_lhs_463_, 1);
lean_inc_ref(v_binderType_579_);
v_body_580_ = lean_ctor_get(v_lhs_463_, 2);
lean_inc_ref(v_body_580_);
v_binderInfo_581_ = lean_ctor_get_uint8(v_lhs_463_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_463_, 3);
v_binderType_582_ = lean_ctor_get(v_rhs_464_, 1);
lean_inc_ref(v_binderType_582_);
v_body_583_ = lean_ctor_get(v_rhs_464_, 2);
lean_inc_ref(v_body_583_);
lean_dec_ref_known(v_rhs_464_, 3);
v___x_584_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_579_, v_binderType_582_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
if (lean_obj_tag(v_a_585_) == 0)
{
lean_dec_ref(v_body_583_);
lean_dec_ref(v_body_580_);
lean_dec(v_binderName_578_);
return v___x_584_;
}
else
{
lean_object* v_val_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_inc_ref(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v_val_586_ = lean_ctor_get(v_a_585_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v_a_585_, 1);
v_fst_587_ = lean_ctor_get(v_val_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_val_586_, 1);
lean_inc(v_snd_588_);
lean_dec(v_val_586_);
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v___y_527_, v___x_589_);
v___x_591_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_580_, v_body_583_, v___x_590_, v_snd_588_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___x_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
if (lean_obj_tag(v_a_592_) == 0)
{
lean_dec(v_fst_587_);
lean_dec(v_binderName_578_);
return v___x_591_;
}
else
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_617_; 
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_618_);
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_617_;
goto v_resetjp_593_;
}
else
{
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_617_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_616_; 
v_val_596_ = lean_ctor_get(v_a_592_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_592_);
if (v_isSharedCheck_616_ == 0)
{
v___x_598_ = v_a_592_;
v_isShared_599_ = v_isSharedCheck_616_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v_a_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_616_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_615_; 
v_fst_600_ = lean_ctor_get(v_val_596_, 0);
v_snd_601_ = lean_ctor_get(v_val_596_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_val_596_);
if (v_isSharedCheck_615_ == 0)
{
v___x_603_ = v_val_596_;
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snd_601_);
lean_inc(v_fst_600_);
lean_dec(v_val_596_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_mkLambda(v_binderName_578_, v_binderInfo_581_, v_fst_587_, v_fst_600_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_snd_601_);
v___x_607_ = v_reuseFailAlloc_614_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_607_);
v___x_609_ = v___x_598_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_609_);
v___x_611_ = v___x_594_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
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
lean_dec(v_fst_587_);
lean_dec(v_binderName_578_);
return v___x_591_;
}
}
}
else
{
lean_dec_ref(v_body_583_);
lean_dec_ref(v_body_580_);
lean_dec(v_binderName_578_);
return v___x_584_;
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref_known(v_lhs_463_, 3);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
case 7:
{
if (lean_obj_tag(v_rhs_464_) == 7)
{
lean_object* v_binderName_621_; lean_object* v_binderType_622_; lean_object* v_body_623_; uint8_t v_binderInfo_624_; lean_object* v_binderType_625_; lean_object* v_body_626_; lean_object* v___x_627_; 
v_binderName_621_ = lean_ctor_get(v_lhs_463_, 0);
lean_inc(v_binderName_621_);
v_binderType_622_ = lean_ctor_get(v_lhs_463_, 1);
lean_inc_ref(v_binderType_622_);
v_body_623_ = lean_ctor_get(v_lhs_463_, 2);
lean_inc_ref(v_body_623_);
v_binderInfo_624_ = lean_ctor_get_uint8(v_lhs_463_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_lhs_463_, 3);
v_binderType_625_ = lean_ctor_get(v_rhs_464_, 1);
lean_inc_ref(v_binderType_625_);
v_body_626_ = lean_ctor_get(v_rhs_464_, 2);
lean_inc_ref(v_body_626_);
lean_dec_ref_known(v_rhs_464_, 3);
v___x_627_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_622_, v_binderType_625_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
if (lean_obj_tag(v_a_628_) == 0)
{
lean_dec_ref(v_body_626_);
lean_dec_ref(v_body_623_);
lean_dec(v_binderName_621_);
return v___x_627_;
}
else
{
lean_object* v_val_629_; lean_object* v_fst_630_; lean_object* v_snd_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_inc_ref(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v_val_629_ = lean_ctor_get(v_a_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v_a_628_, 1);
v_fst_630_ = lean_ctor_get(v_val_629_, 0);
lean_inc(v_fst_630_);
v_snd_631_ = lean_ctor_get(v_val_629_, 1);
lean_inc(v_snd_631_);
lean_dec(v_val_629_);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v___y_527_, v___x_632_);
v___x_634_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_623_, v_body_626_, v___x_633_, v_snd_631_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
if (lean_obj_tag(v_a_635_) == 0)
{
lean_dec(v_fst_630_);
lean_dec(v_binderName_621_);
return v___x_634_;
}
else
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_660_; 
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_661_);
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_660_;
goto v_resetjp_636_;
}
else
{
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_660_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_659_; 
v_val_639_ = lean_ctor_get(v_a_635_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_a_635_);
if (v_isSharedCheck_659_ == 0)
{
v___x_641_ = v_a_635_;
v_isShared_642_ = v_isSharedCheck_659_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_dec(v_a_635_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_659_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_658_; 
v_fst_643_ = lean_ctor_get(v_val_639_, 0);
v_snd_644_ = lean_ctor_get(v_val_639_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_val_639_);
if (v_isSharedCheck_658_ == 0)
{
v___x_646_ = v_val_639_;
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_643_);
lean_dec(v_val_639_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = l_Lean_mkForall(v_binderName_621_, v_binderInfo_624_, v_fst_630_, v_fst_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_snd_644_);
v___x_650_ = v_reuseFailAlloc_657_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_650_);
v___x_652_ = v___x_641_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_652_);
v___x_654_ = v___x_637_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
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
lean_dec(v_fst_630_);
lean_dec(v_binderName_621_);
return v___x_634_;
}
}
}
else
{
lean_dec_ref(v_body_626_);
lean_dec_ref(v_body_623_);
lean_dec(v_binderName_621_);
return v___x_627_;
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref_known(v_lhs_463_, 3);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
case 8:
{
if (lean_obj_tag(v_rhs_464_) == 8)
{
lean_object* v_declName_664_; lean_object* v_type_665_; lean_object* v_value_666_; lean_object* v_body_667_; uint8_t v_nondep_668_; lean_object* v_type_669_; lean_object* v_value_670_; lean_object* v_body_671_; lean_object* v___x_672_; 
v_declName_664_ = lean_ctor_get(v_lhs_463_, 0);
lean_inc(v_declName_664_);
v_type_665_ = lean_ctor_get(v_lhs_463_, 1);
lean_inc_ref(v_type_665_);
v_value_666_ = lean_ctor_get(v_lhs_463_, 2);
lean_inc_ref(v_value_666_);
v_body_667_ = lean_ctor_get(v_lhs_463_, 3);
lean_inc_ref(v_body_667_);
v_nondep_668_ = lean_ctor_get_uint8(v_lhs_463_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_lhs_463_, 4);
v_type_669_ = lean_ctor_get(v_rhs_464_, 1);
lean_inc_ref(v_type_669_);
v_value_670_ = lean_ctor_get(v_rhs_464_, 2);
lean_inc_ref(v_value_670_);
v_body_671_ = lean_ctor_get(v_rhs_464_, 3);
lean_inc_ref(v_body_671_);
lean_dec_ref_known(v_rhs_464_, 4);
v___x_672_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_type_665_, v_type_669_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
if (lean_obj_tag(v_a_673_) == 0)
{
lean_dec_ref(v_body_671_);
lean_dec_ref(v_value_670_);
lean_dec_ref(v_body_667_);
lean_dec_ref(v_value_666_);
lean_dec(v_declName_664_);
return v___x_672_;
}
else
{
lean_object* v_val_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_677_; 
lean_inc_ref(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v_val_674_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_a_673_, 1);
v_fst_675_ = lean_ctor_get(v_val_674_, 0);
lean_inc(v_fst_675_);
v_snd_676_ = lean_ctor_get(v_val_674_, 1);
lean_inc(v_snd_676_);
lean_dec(v_val_674_);
v___x_677_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_value_666_, v_value_670_, v___y_527_, v_snd_676_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
if (lean_obj_tag(v_a_678_) == 0)
{
lean_dec(v_fst_675_);
lean_dec_ref(v_body_671_);
lean_dec_ref(v_body_667_);
lean_dec(v_declName_664_);
return v___x_677_;
}
else
{
lean_object* v_val_679_; lean_object* v_fst_680_; lean_object* v_snd_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc_ref(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v_val_679_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_a_678_, 1);
v_fst_680_ = lean_ctor_get(v_val_679_, 0);
lean_inc(v_fst_680_);
v_snd_681_ = lean_ctor_get(v_val_679_, 1);
lean_inc(v_snd_681_);
lean_dec(v_val_679_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v___y_527_, v___x_682_);
v___x_684_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_667_, v_body_671_, v___x_683_, v_snd_681_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___x_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
if (lean_obj_tag(v_a_685_) == 0)
{
lean_dec(v_fst_680_);
lean_dec(v_fst_675_);
lean_dec(v_declName_664_);
return v___x_684_;
}
else
{
lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_710_; 
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_711_);
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_710_;
goto v_resetjp_686_;
}
else
{
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_710_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_val_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_709_; 
v_val_689_ = lean_ctor_get(v_a_685_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_a_685_);
if (v_isSharedCheck_709_ == 0)
{
v___x_691_ = v_a_685_;
v_isShared_692_ = v_isSharedCheck_709_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_val_689_);
lean_dec(v_a_685_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_709_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_708_; 
v_fst_693_ = lean_ctor_get(v_val_689_, 0);
v_snd_694_ = lean_ctor_get(v_val_689_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_val_689_);
if (v_isSharedCheck_708_ == 0)
{
v___x_696_ = v_val_689_;
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_dec(v_val_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_Expr_letE___override(v_declName_664_, v_fst_675_, v_fst_680_, v_fst_693_, v_nondep_668_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_snd_694_);
v___x_700_ = v_reuseFailAlloc_707_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_700_);
v___x_702_ = v___x_691_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_702_);
v___x_704_ = v___x_687_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
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
lean_dec(v_fst_680_);
lean_dec(v_fst_675_);
lean_dec(v_declName_664_);
return v___x_684_;
}
}
}
else
{
lean_dec(v_fst_675_);
lean_dec_ref(v_body_671_);
lean_dec_ref(v_body_667_);
lean_dec(v_declName_664_);
return v___x_677_;
}
}
}
else
{
lean_dec_ref(v_body_671_);
lean_dec_ref(v_value_670_);
lean_dec_ref(v_body_667_);
lean_dec_ref(v_value_666_);
lean_dec(v_declName_664_);
return v___x_672_;
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref_known(v_lhs_463_, 4);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
case 10:
{
if (lean_obj_tag(v_rhs_464_) == 10)
{
lean_object* v_data_714_; lean_object* v_expr_715_; lean_object* v_expr_716_; lean_object* v___x_717_; 
v_data_714_ = lean_ctor_get(v_lhs_463_, 0);
lean_inc(v_data_714_);
v_expr_715_ = lean_ctor_get(v_lhs_463_, 1);
lean_inc_ref(v_expr_715_);
lean_dec_ref_known(v_lhs_463_, 2);
v_expr_716_ = lean_ctor_get(v_rhs_464_, 1);
lean_inc_ref(v_expr_716_);
lean_dec_ref_known(v_rhs_464_, 2);
v___x_717_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_expr_715_, v_expr_716_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
if (lean_obj_tag(v_a_718_) == 0)
{
lean_dec(v_data_714_);
return v___x_717_;
}
else
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_743_; 
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_744_);
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_743_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_743_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_val_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_742_; 
v_val_722_ = lean_ctor_get(v_a_718_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_718_);
if (v_isSharedCheck_742_ == 0)
{
v___x_724_ = v_a_718_;
v_isShared_725_ = v_isSharedCheck_742_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_val_722_);
lean_dec(v_a_718_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_742_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_741_; 
v_fst_726_ = lean_ctor_get(v_val_722_, 0);
v_snd_727_ = lean_ctor_get(v_val_722_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_val_722_);
if (v_isSharedCheck_741_ == 0)
{
v___x_729_ = v_val_722_;
v_isShared_730_ = v_isSharedCheck_741_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_val_722_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_741_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = l_Lean_Expr_mdata___override(v_data_714_, v_fst_726_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_snd_727_);
v___x_733_ = v_reuseFailAlloc_740_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_733_);
v___x_735_ = v___x_724_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_735_);
v___x_737_ = v___x_720_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
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
}
}
}
}
else
{
lean_dec(v_data_714_);
return v___x_717_;
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref_known(v_lhs_463_, 2);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
case 11:
{
if (lean_obj_tag(v_rhs_464_) == 11)
{
lean_object* v_typeName_747_; lean_object* v_idx_748_; lean_object* v_struct_749_; lean_object* v_typeName_750_; lean_object* v_idx_751_; lean_object* v_struct_752_; uint8_t v___x_753_; 
v_typeName_747_ = lean_ctor_get(v_lhs_463_, 0);
lean_inc(v_typeName_747_);
v_idx_748_ = lean_ctor_get(v_lhs_463_, 1);
lean_inc(v_idx_748_);
v_struct_749_ = lean_ctor_get(v_lhs_463_, 2);
lean_inc_ref(v_struct_749_);
lean_dec_ref_known(v_lhs_463_, 3);
v_typeName_750_ = lean_ctor_get(v_rhs_464_, 0);
lean_inc(v_typeName_750_);
v_idx_751_ = lean_ctor_get(v_rhs_464_, 1);
lean_inc(v_idx_751_);
v_struct_752_ = lean_ctor_get(v_rhs_464_, 2);
lean_inc_ref(v_struct_752_);
lean_dec_ref_known(v_rhs_464_, 3);
v___x_753_ = lean_name_eq(v_typeName_747_, v_typeName_750_);
lean_dec(v_typeName_750_);
if (v___x_753_ == 0)
{
lean_dec(v_idx_751_);
v___y_479_ = v___y_531_;
v___y_480_ = v___y_532_;
v___y_481_ = v_struct_752_;
v___y_482_ = v___y_528_;
v___y_483_ = v___y_529_;
v___y_484_ = v___y_538_;
v___y_485_ = v___y_527_;
v___y_486_ = v___y_533_;
v___y_487_ = v_typeName_747_;
v___y_488_ = v___y_535_;
v___y_489_ = v___y_536_;
v___y_490_ = v_idx_748_;
v___y_491_ = v___y_537_;
v___y_492_ = v___y_530_;
v___y_493_ = v___y_534_;
v___y_494_ = v_struct_749_;
v___y_495_ = v___x_753_;
goto v___jp_478_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = lean_nat_dec_eq(v_idx_748_, v_idx_751_);
lean_dec(v_idx_751_);
v___y_479_ = v___y_531_;
v___y_480_ = v___y_532_;
v___y_481_ = v_struct_752_;
v___y_482_ = v___y_528_;
v___y_483_ = v___y_529_;
v___y_484_ = v___y_538_;
v___y_485_ = v___y_527_;
v___y_486_ = v___y_533_;
v___y_487_ = v_typeName_747_;
v___y_488_ = v___y_535_;
v___y_489_ = v___y_536_;
v___y_490_ = v_idx_748_;
v___y_491_ = v___y_537_;
v___y_492_ = v___y_530_;
v___y_493_ = v___y_534_;
v___y_494_ = v_struct_749_;
v___y_495_ = v___x_754_;
goto v___jp_478_;
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref_known(v_lhs_463_, 3);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
default: 
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref(v___y_528_);
lean_dec_ref(v_rhs_464_);
lean_dec_ref(v_lhs_463_);
v___x_757_ = lean_box(0);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_463_ = stack[0].m_obj;
lean_object* v_rhs_464_ = stack[1].m_obj;
lean_object* v_a_465_ = stack[2].m_obj;
lean_object* v_a_466_ = stack[3].m_obj;
lean_object* v_a_467_ = stack[4].m_obj;
lean_object* v_a_468_ = stack[5].m_obj;
lean_object* v_a_469_ = stack[6].m_obj;
lean_object* v_a_470_ = stack[7].m_obj;
lean_object* v_a_471_ = stack[8].m_obj;
lean_object* v_a_472_ = stack[9].m_obj;
lean_object* v_a_473_ = stack[10].m_obj;
lean_object* v_a_474_ = stack[11].m_obj;
lean_object* v_a_475_ = stack[12].m_obj;
lean_object* v_a_476_ = stack[13].m_obj;
lean_object* v_res_884_;
v_res_884_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_463_, v_rhs_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
stack->m_obj
 = v_res_884_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object* v_lhs_885_, lean_object* v_rhs_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
size_t v___x_900_; size_t v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_ptr_addr(v_lhs_885_);
v___x_901_ = lean_ptr_addr(v_rhs_886_);
v___x_902_ = lean_usize_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v_cache_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_cache_903_ = lean_ctor_get(v_a_888_, 0);
lean_inc_ref(v_rhs_886_);
lean_inc_ref(v_lhs_885_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_lhs_885_);
lean_ctor_set(v___x_904_, 1, v_rhs_886_);
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_903_, v___x_904_);
if (lean_obj_tag(v___x_905_) == 1)
{
lean_object* v_val_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref_known(v___x_904_, 2);
lean_dec_ref(v_rhs_886_);
lean_dec_ref(v_lhs_885_);
v_val_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_915_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_val_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_val_906_);
lean_ctor_set(v___x_910_, 1, v_a_888_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_914_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
else
{
lean_object* v___x_916_; 
lean_dec(v___x_905_);
v___x_916_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_885_, v_rhs_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
if (lean_obj_tag(v_a_917_) == 0)
{
lean_dec_ref_known(v___x_904_, 2);
return v___x_916_;
}
else
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_953_; 
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v___x_916_, 0);
lean_dec(v_unused_954_);
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_953_;
goto v_resetjp_918_;
}
else
{
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_953_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_val_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_952_; 
v_val_921_ = lean_ctor_get(v_a_917_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_a_917_);
if (v_isSharedCheck_952_ == 0)
{
v___x_923_ = v_a_917_;
v_isShared_924_ = v_isSharedCheck_952_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_val_921_);
lean_dec(v_a_917_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_952_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_snd_925_; lean_object* v_fst_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_951_; 
v_snd_925_ = lean_ctor_get(v_val_921_, 1);
v_fst_926_ = lean_ctor_get(v_val_921_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_val_921_);
if (v_isSharedCheck_951_ == 0)
{
v___x_928_ = v_val_921_;
v_isShared_929_ = v_isSharedCheck_951_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_926_);
lean_dec(v_val_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_951_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_cache_930_; lean_object* v_varTypes_931_; lean_object* v_lhss_932_; lean_object* v_rhss_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_950_; 
v_cache_930_ = lean_ctor_get(v_snd_925_, 0);
v_varTypes_931_ = lean_ctor_get(v_snd_925_, 1);
v_lhss_932_ = lean_ctor_get(v_snd_925_, 2);
v_rhss_933_ = lean_ctor_get(v_snd_925_, 3);
v_isSharedCheck_950_ = !lean_is_exclusive(v_snd_925_);
if (v_isSharedCheck_950_ == 0)
{
v___x_935_ = v_snd_925_;
v_isShared_936_ = v_isSharedCheck_950_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_rhss_933_);
lean_inc(v_lhss_932_);
lean_inc(v_varTypes_931_);
lean_inc(v_cache_930_);
lean_dec(v_snd_925_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_950_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
lean_inc(v_fst_926_);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_930_, v___x_904_, v_fst_926_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_varTypes_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_lhss_932_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_rhss_933_);
v___x_939_ = v_reuseFailAlloc_949_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_939_);
v___x_941_ = v___x_928_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_fst_926_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_939_);
v___x_941_ = v_reuseFailAlloc_948_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_941_);
v___x_943_ = v___x_923_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_943_);
v___x_945_ = v___x_919_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
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
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_904_, 2);
return v___x_916_;
}
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref(v_rhs_886_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_lhs_885_);
lean_ctor_set(v___x_955_, 1, v_a_888_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_885_ = stack[0].m_obj;
lean_object* v_rhs_886_ = stack[1].m_obj;
lean_object* v_a_887_ = stack[2].m_obj;
lean_object* v_a_888_ = stack[3].m_obj;
lean_object* v_a_889_ = stack[4].m_obj;
lean_object* v_a_890_ = stack[5].m_obj;
lean_object* v_a_891_ = stack[6].m_obj;
lean_object* v_a_892_ = stack[7].m_obj;
lean_object* v_a_893_ = stack[8].m_obj;
lean_object* v_a_894_ = stack[9].m_obj;
lean_object* v_a_895_ = stack[10].m_obj;
lean_object* v_a_896_ = stack[11].m_obj;
lean_object* v_a_897_ = stack[12].m_obj;
lean_object* v_a_898_ = stack[13].m_obj;
lean_object* v_res_958_;
v_res_958_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_885_, v_rhs_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(lean_object* v_lhs_959_, lean_object* v_rhs_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_959_, v_rhs_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec(v_a_963_);
lean_dec(v_a_961_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(lean_object* v_lhs_975_, lean_object* v_rhs_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_975_, v_rhs_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec(v_a_979_);
lean_dec(v_a_977_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(lean_object* v_00_u03b2_991_, lean_object* v_m_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_992_, v_a_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(lean_object* v_00_u03b2_995_, lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(v_00_u03b2_995_, v_m_996_, v_a_997_);
lean_dec_ref(v_a_997_);
lean_dec_ref(v_m_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(lean_object* v_00_u03b2_999_, lean_object* v_m_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_1000_, v_a_1001_, v_b_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(lean_object* v_00_u03b2_1004_, lean_object* v_a_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_1005_, v_x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1008_, lean_object* v_a_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(v_00_u03b2_1008_, v_a_1009_, v_x_1010_);
lean_dec(v_x_1010_);
lean_dec_ref(v_a_1009_);
return v_res_1011_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object* v_00_u03b2_1012_, lean_object* v_a_1013_, lean_object* v_x_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1013_ = stack[1].m_obj;
lean_object* v_x_1014_ = stack[2].m_obj;
uint8_t v_res_1016_;
v_res_1016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_box(0), v_a_1013_, v_x_1014_);
stack->m_num = v_res_1016_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_a_1018_, lean_object* v_x_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_1017_, v_a_1018_, v_x_1019_);
lean_dec(v_x_1019_);
lean_dec_ref(v_a_1018_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(lean_object* v_00_u03b2_1022_, lean_object* v_data_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_data_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(lean_object* v_00_u03b2_1025_, lean_object* v_a_1026_, lean_object* v_b_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_1026_, v_b_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1030_, lean_object* v_i_1031_, lean_object* v_source_1032_, lean_object* v_target_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v_i_1031_, v_source_1032_, v_target_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1036_, v_x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_unsigned_to_nat(16u);
v___x_1041_ = lean_mk_array(v___x_1040_, v___x_1039_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1042_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2));
v___x_1048_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
v___x_1049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_1047_);
lean_ctor_set(v___x_1049_, 3, v___x_1047_);
return v___x_1049_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object* v_lhs_1057_, lean_object* v_rhs_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Meta_Sym_shareCommon(v_lhs_1057_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = l_Lean_Meta_Sym_shareCommon(v_rhs_1058_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_1071_, v_a_1073_, v___x_1074_, v___x_1075_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1146_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1146_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1146_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
if (lean_obj_tag(v_a_1077_) == 1)
{
lean_object* v_val_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1141_; 
v_val_1081_ = lean_ctor_get(v_a_1077_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1083_ = v_a_1077_;
v_isShared_1084_ = v_isSharedCheck_1141_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_val_1081_);
lean_dec(v_a_1077_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1141_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_snd_1085_; lean_object* v_fst_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1140_; 
v_snd_1085_ = lean_ctor_get(v_val_1081_, 1);
v_fst_1086_ = lean_ctor_get(v_val_1081_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_val_1081_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1088_ = v_val_1081_;
v_isShared_1089_ = v_isSharedCheck_1140_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1085_);
lean_inc(v_fst_1086_);
lean_dec(v_val_1081_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1140_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_varTypes_1090_; lean_object* v_lhss_1091_; lean_object* v_rhss_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_varTypes_1090_ = lean_ctor_get(v_snd_1085_, 1);
lean_inc_ref(v_varTypes_1090_);
v_lhss_1091_ = lean_ctor_get(v_snd_1085_, 2);
lean_inc_ref(v_lhss_1091_);
v_rhss_1092_ = lean_ctor_get(v_snd_1085_, 3);
lean_inc_ref(v_rhss_1092_);
lean_dec(v_snd_1085_);
v___x_1093_ = lean_array_get_size(v_lhss_1091_);
v___x_1094_ = lean_nat_dec_eq(v___x_1093_, v___x_1074_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_del_object(v___x_1079_);
v___x_1095_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_1090_, v_fst_1086_);
lean_dec_ref(v_varTypes_1090_);
lean_inc(v_a_1068_);
lean_inc_ref(v_a_1067_);
lean_inc(v_a_1066_);
lean_inc_ref(v_a_1065_);
lean_inc_ref(v___x_1095_);
v___x_1096_ = lean_infer_type(v___x_1095_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_n(v_a_1097_, 2);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l_Lean_Meta_getLevel(v_a_1097_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1119_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7));
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_a_1099_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_Expr_const___override(v___x_1103_, v___x_1105_);
v___x_1107_ = l_Lean_mkAppB(v___x_1106_, v_a_1097_, v___x_1095_);
lean_inc_ref(v___x_1107_);
v___x_1108_ = l_Lean_mkAppN(v___x_1107_, v_lhss_1091_);
lean_dec_ref(v_lhss_1091_);
v___x_1109_ = l_Lean_mkAppN(v___x_1107_, v_rhss_1092_);
lean_dec_ref(v_rhss_1092_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1109_);
lean_ctor_set(v___x_1088_, 0, v___x_1108_);
v___x_1111_ = v___x_1088_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1111_);
v___x_1113_ = v___x_1083_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1113_);
v___x_1115_ = v___x_1101_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_a_1097_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_rhss_1092_);
lean_dec_ref(v_lhss_1091_);
lean_del_object(v___x_1088_);
lean_del_object(v___x_1083_);
v_a_1120_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1098_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1098_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_rhss_1092_);
lean_dec_ref(v_lhss_1091_);
lean_del_object(v___x_1088_);
lean_del_object(v___x_1083_);
v_a_1128_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1096_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1096_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec_ref(v_rhss_1092_);
lean_dec_ref(v_lhss_1091_);
lean_dec_ref(v_varTypes_1090_);
lean_del_object(v___x_1088_);
lean_dec(v_fst_1086_);
lean_del_object(v___x_1083_);
v___x_1136_ = lean_box(0);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1136_);
v___x_1138_ = v___x_1079_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
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
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec(v_a_1077_);
v___x_1142_ = lean_box(0);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1142_);
v___x_1144_ = v___x_1079_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1076_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1076_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_a_1071_);
v_a_1155_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1072_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1072_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_rhs_1058_);
v_a_1163_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1070_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1070_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1057_ = stack[0].m_obj;
lean_object* v_rhs_1058_ = stack[1].m_obj;
lean_object* v_a_1059_ = stack[2].m_obj;
lean_object* v_a_1060_ = stack[3].m_obj;
lean_object* v_a_1061_ = stack[4].m_obj;
lean_object* v_a_1062_ = stack[5].m_obj;
lean_object* v_a_1063_ = stack[6].m_obj;
lean_object* v_a_1064_ = stack[7].m_obj;
lean_object* v_a_1065_ = stack[8].m_obj;
lean_object* v_a_1066_ = stack[9].m_obj;
lean_object* v_a_1067_ = stack[10].m_obj;
lean_object* v_a_1068_ = stack[11].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_1057_, v_rhs_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
stack->m_obj
 = v_res_1171_;
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(lean_object* v_msgData_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; uint8_t v___x_1194_; lean_object* v_env_1195_; lean_object* v___x_1196_; lean_object* v_toCold_1197_; lean_object* v_mctx_1198_; lean_object* v_lctx_1199_; lean_object* v_options_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1194_ = 0;
v_env_1195_ = l_Lean_Environment_setRecordingDeps(v_env_1193_, v___x_1194_);
v___x_1196_ = lean_st_ref_get(v___y_1188_);
v_toCold_1197_ = lean_ctor_get(v___y_1189_, 0);
v_mctx_1198_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_mctx_1198_);
lean_dec(v___x_1196_);
v_lctx_1199_ = lean_ctor_get(v___y_1187_, 2);
v_options_1200_ = lean_ctor_get(v_toCold_1197_, 2);
lean_inc_ref(v_options_1200_);
lean_inc_ref(v_lctx_1199_);
v___x_1201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1201_, 0, v_env_1195_);
lean_ctor_set(v___x_1201_, 1, v_mctx_1198_);
lean_ctor_set(v___x_1201_, 2, v_lctx_1199_);
lean_ctor_set(v___x_1201_, 3, v_options_1200_);
v___x_1202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_msgData_1186_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1186_ = stack[0].m_obj;
lean_object* v___y_1187_ = stack[1].m_obj;
lean_object* v___y_1188_ = stack[2].m_obj;
lean_object* v___y_1189_ = stack[3].m_obj;
lean_object* v___y_1190_ = stack[4].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(lean_object* v_msgData_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1211_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1212_; double v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_float_of_nat(v___x_1212_);
return v___x_1213_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object* v_cls_1217_, lean_object* v_msg_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_ref_1224_; lean_object* v___x_1225_; lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1271_; 
v_ref_1224_ = lean_ctor_get(v___y_1221_, 2);
v___x_1225_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1271_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1271_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v_traceState_1231_; lean_object* v_env_1232_; lean_object* v_nextMacroScope_1233_; lean_object* v_ngen_1234_; lean_object* v_auxDeclNGen_1235_; lean_object* v_cache_1236_; lean_object* v_recordedDeps_1237_; lean_object* v_messages_1238_; lean_object* v_infoState_1239_; lean_object* v_snapshotTasks_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1270_; 
v___x_1230_ = lean_st_ref_take(v___y_1222_);
v_traceState_1231_ = lean_ctor_get(v___x_1230_, 4);
v_env_1232_ = lean_ctor_get(v___x_1230_, 0);
v_nextMacroScope_1233_ = lean_ctor_get(v___x_1230_, 1);
v_ngen_1234_ = lean_ctor_get(v___x_1230_, 2);
v_auxDeclNGen_1235_ = lean_ctor_get(v___x_1230_, 3);
v_cache_1236_ = lean_ctor_get(v___x_1230_, 5);
v_recordedDeps_1237_ = lean_ctor_get(v___x_1230_, 6);
v_messages_1238_ = lean_ctor_get(v___x_1230_, 7);
v_infoState_1239_ = lean_ctor_get(v___x_1230_, 8);
v_snapshotTasks_1240_ = lean_ctor_get(v___x_1230_, 9);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1242_ = v___x_1230_;
v_isShared_1243_ = v_isSharedCheck_1270_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snapshotTasks_1240_);
lean_inc(v_infoState_1239_);
lean_inc(v_messages_1238_);
lean_inc(v_recordedDeps_1237_);
lean_inc(v_cache_1236_);
lean_inc(v_traceState_1231_);
lean_inc(v_auxDeclNGen_1235_);
lean_inc(v_ngen_1234_);
lean_inc(v_nextMacroScope_1233_);
lean_inc(v_env_1232_);
lean_dec(v___x_1230_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1270_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint64_t v_tid_1244_; lean_object* v_traces_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1269_; 
v_tid_1244_ = lean_ctor_get_uint64(v_traceState_1231_, sizeof(void*)*1);
v_traces_1245_ = lean_ctor_get(v_traceState_1231_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_traceState_1231_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1247_ = v_traceState_1231_;
v_isShared_1248_ = v_isSharedCheck_1269_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_traces_1245_);
lean_dec(v_traceState_1231_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1269_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; double v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
v___x_1252_ = 0;
v___x_1253_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1));
v___x_1254_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1254_, 0, v_cls_1217_);
lean_ctor_set(v___x_1254_, 1, v___x_1250_);
lean_ctor_set(v___x_1254_, 2, v___x_1253_);
lean_ctor_set_float(v___x_1254_, sizeof(void*)*3, v___x_1251_);
lean_ctor_set_float(v___x_1254_, sizeof(void*)*3 + 8, v___x_1251_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*3 + 16, v___x_1252_);
v___x_1255_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2));
v___x_1256_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v_a_1226_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
lean_inc(v_ref_1224_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_ref_1224_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = l_Lean_PersistentArray_push___redArg(v_traces_1245_, v___x_1257_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1258_);
v___x_1260_ = v___x_1247_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1258_);
lean_ctor_set_uint64(v_reuseFailAlloc_1268_, sizeof(void*)*1, v_tid_1244_);
v___x_1260_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___x_1260_);
v___x_1262_ = v___x_1242_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_env_1232_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_nextMacroScope_1233_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_ngen_1234_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_auxDeclNGen_1235_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1267_, 5, v_cache_1236_);
lean_ctor_set(v_reuseFailAlloc_1267_, 6, v_recordedDeps_1237_);
lean_ctor_set(v_reuseFailAlloc_1267_, 7, v_messages_1238_);
lean_ctor_set(v_reuseFailAlloc_1267_, 8, v_infoState_1239_);
lean_ctor_set(v_reuseFailAlloc_1267_, 9, v_snapshotTasks_1240_);
v___x_1262_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = lean_st_ref_put(v___y_1222_, v___x_1262_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1249_);
v___x_1265_ = v___x_1228_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1249_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1217_ = stack[0].m_obj;
lean_object* v_msg_1218_ = stack[1].m_obj;
lean_object* v___y_1219_ = stack[2].m_obj;
lean_object* v___y_1220_ = stack[3].m_obj;
lean_object* v___y_1221_ = stack[4].m_obj;
lean_object* v___y_1222_ = stack[5].m_obj;
lean_object* v_res_1272_;
v_res_1272_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1217_, v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
stack->m_obj
 = v_res_1272_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object* v_cls_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1273_, v_msg_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5));
v___x_1293_ = l_Lean_Name_append(v___x_1292_, v___x_1291_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object* v_lhs_u2080_1303_, lean_object* v_rhs_u2080_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_1303_, v_rhs_u2080_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1442_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1442_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1442_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
if (lean_obj_tag(v_a_1317_) == 1)
{
lean_object* v_val_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1319_);
v_val_1321_ = lean_ctor_get(v_a_1317_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1317_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1323_ = v_a_1317_;
v_isShared_1324_ = v_isSharedCheck_1437_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_val_1321_);
lean_dec(v_a_1317_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1437_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_fst_1325_; lean_object* v_snd_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1436_; 
v_fst_1325_ = lean_ctor_get(v_val_1321_, 0);
v_snd_1326_ = lean_ctor_get(v_val_1321_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_val_1321_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1328_ = v_val_1321_;
v_isShared_1329_ = v_isSharedCheck_1436_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snd_1326_);
lean_inc(v_fst_1325_);
lean_dec(v_val_1321_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1436_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v_toCold_1409_; lean_object* v_options_1410_; uint8_t v_hasTrace_1411_; 
v_toCold_1409_ = lean_ctor_get(v_a_1313_, 0);
v_options_1410_ = lean_ctor_get(v_toCold_1409_, 2);
v_hasTrace_1411_ = lean_ctor_get_uint8(v_options_1410_, sizeof(void*)*1);
if (v_hasTrace_1411_ == 0)
{
lean_del_object(v___x_1328_);
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
v___y_1334_ = v_a_1308_;
v___y_1335_ = v_a_1309_;
v___y_1336_ = v_a_1310_;
v___y_1337_ = v_a_1311_;
v___y_1338_ = v_a_1312_;
v___y_1339_ = v_a_1313_;
v___y_1340_ = v_a_1314_;
goto v___jp_1330_;
}
else
{
lean_object* v_inheritedTraceOptions_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_inheritedTraceOptions_1412_ = lean_ctor_get(v_toCold_1409_, 11);
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1412_, v_options_1410_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_del_object(v___x_1328_);
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
v___y_1334_ = v_a_1308_;
v___y_1335_ = v_a_1309_;
v___y_1336_ = v_a_1310_;
v___y_1337_ = v_a_1311_;
v___y_1338_ = v_a_1312_;
v___y_1339_ = v_a_1313_;
v___y_1340_ = v_a_1314_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
lean_inc(v_fst_1325_);
v___x_1417_ = l_Lean_MessageData_ofExpr(v_fst_1325_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 7);
lean_ctor_set(v___x_1328_, 1, v___x_1417_);
lean_ctor_set(v___x_1328_, 0, v___x_1416_);
v___x_1419_ = v___x_1328_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
lean_inc(v_snd_1326_);
v___x_1422_ = l_Lean_MessageData_ofExpr(v_snd_1326_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_1413_, v___x_1425_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_dec_ref_known(v___x_1426_, 1);
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
v___y_1334_ = v_a_1308_;
v___y_1335_ = v_a_1309_;
v___y_1336_ = v_a_1310_;
v___y_1337_ = v_a_1311_;
v___y_1338_ = v_a_1312_;
v___y_1339_ = v_a_1313_;
v___y_1340_ = v_a_1314_;
goto v___jp_1330_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_snd_1326_);
lean_dec(v_fst_1325_);
lean_del_object(v___x_1323_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
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
v___jp_1330_:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_1325_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1343_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_1326_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc(v___y_1331_);
v___x_1345_ = lean_grind_process_to_do(v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref_known(v___x_1345_, 1);
v___x_1346_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1342_, v_a_1344_, v___y_1331_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1376_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1376_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1376_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_unbox(v_a_1347_);
lean_dec(v_a_1347_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_dec(v_a_1344_);
lean_dec(v_a_1342_);
lean_del_object(v___x_1323_);
v___x_1352_ = lean_box(0);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
lean_object* v___x_1356_; 
lean_del_object(v___x_1349_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc(v___y_1331_);
v___x_1356_ = lean_grind_mk_eq_proof(v_a_1342_, v_a_1344_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1367_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_a_1357_);
v___x_1362_ = v___x_1323_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1323_);
v_a_1368_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1356_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1356_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_a_1344_);
lean_dec(v_a_1342_);
lean_del_object(v___x_1323_);
v_a_1377_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1346_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1346_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_a_1344_);
lean_dec(v_a_1342_);
lean_del_object(v___x_1323_);
v_a_1385_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1345_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1345_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_a_1342_);
lean_del_object(v___x_1323_);
v_a_1393_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1343_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1343_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec(v_snd_1326_);
lean_del_object(v___x_1323_);
v_a_1401_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1341_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1341_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec(v_a_1317_);
v___x_1438_ = lean_box(0);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1438_);
v___x_1440_ = v___x_1319_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_a_1443_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1316_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1316_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_u2080_1303_ = stack[0].m_obj;
lean_object* v_rhs_u2080_1304_ = stack[1].m_obj;
lean_object* v_a_1305_ = stack[2].m_obj;
lean_object* v_a_1306_ = stack[3].m_obj;
lean_object* v_a_1307_ = stack[4].m_obj;
lean_object* v_a_1308_ = stack[5].m_obj;
lean_object* v_a_1309_ = stack[6].m_obj;
lean_object* v_a_1310_ = stack[7].m_obj;
lean_object* v_a_1311_ = stack[8].m_obj;
lean_object* v_a_1312_ = stack[9].m_obj;
lean_object* v_a_1313_ = stack[10].m_obj;
lean_object* v_a_1314_ = stack[11].m_obj;
lean_object* v_res_1451_;
v_res_1451_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_lhs_u2080_1303_, v_rhs_u2080_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
stack->m_obj
 = v_res_1451_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(lean_object* v_lhs_u2080_1452_, lean_object* v_rhs_u2080_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_lhs_u2080_1452_, v_rhs_u2080_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec(v_a_1454_);
return v_res_1465_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(lean_object* v_cls_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1466_, v_msg_1467_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1466_ = stack[0].m_obj;
lean_object* v_msg_1467_ = stack[1].m_obj;
lean_object* v___y_1468_ = stack[2].m_obj;
lean_object* v___y_1469_ = stack[3].m_obj;
lean_object* v___y_1470_ = stack[4].m_obj;
lean_object* v___y_1471_ = stack[5].m_obj;
lean_object* v___y_1472_ = stack[6].m_obj;
lean_object* v___y_1473_ = stack[7].m_obj;
lean_object* v___y_1474_ = stack[8].m_obj;
lean_object* v___y_1475_ = stack[9].m_obj;
lean_object* v___y_1476_ = stack[10].m_obj;
lean_object* v___y_1477_ = stack[11].m_obj;
lean_object* v_res_1480_;
v_res_1480_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_1466_, v_msg_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
stack->m_obj
 = v_res_1480_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(lean_object* v_cls_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_1481_, v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec(v___y_1483_);
return v_res_1494_;
}
}
lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0(lean_object* v_lhs_1495_, lean_object* v_rhs_1496_, uint8_t v_abstract_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1495_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1496_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc(v___y_1498_);
v___x_1513_ = lean_grind_process_to_do(v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
lean_dec_ref_known(v___x_1513_, 1);
v___x_1514_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1510_, v_a_1512_, v___y_1498_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1543_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1543_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1543_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_unbox(v_a_1515_);
lean_dec(v_a_1515_);
if (v___x_1519_ == 0)
{
if (v_abstract_1497_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_dec(v_a_1512_);
lean_dec(v_a_1510_);
v___x_1520_ = lean_box(0);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1520_);
v___x_1522_ = v___x_1517_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
else
{
lean_object* v___x_1524_; 
lean_del_object(v___x_1517_);
v___x_1524_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_a_1510_, v_a_1512_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1524_;
}
}
else
{
lean_object* v___x_1525_; 
lean_del_object(v___x_1517_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc(v___y_1498_);
v___x_1525_ = lean_grind_mk_eq_proof(v_a_1510_, v_a_1512_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1534_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1534_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1534_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1526_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1532_ = v___x_1528_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1525_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1525_);
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
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1512_);
lean_dec(v_a_1510_);
v_a_1544_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1514_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1514_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1512_);
lean_dec(v_a_1510_);
v_a_1552_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1513_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1513_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_a_1510_);
v_a_1560_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1511_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1511_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_rhs_1496_);
v_a_1568_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1509_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1509_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_proveEq_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1495_ = stack[0].m_obj;
lean_object* v_rhs_1496_ = stack[1].m_obj;
uint8_t v_abstract_1497_ = stack[2].m_num;
lean_object* v___y_1498_ = stack[3].m_obj;
lean_object* v___y_1499_ = stack[4].m_obj;
lean_object* v___y_1500_ = stack[5].m_obj;
lean_object* v___y_1501_ = stack[6].m_obj;
lean_object* v___y_1502_ = stack[7].m_obj;
lean_object* v___y_1503_ = stack[8].m_obj;
lean_object* v___y_1504_ = stack[9].m_obj;
lean_object* v___y_1505_ = stack[10].m_obj;
lean_object* v___y_1506_ = stack[11].m_obj;
lean_object* v___y_1507_ = stack[12].m_obj;
lean_object* v_res_1576_;
v_res_1576_ = l_Lean_Meta_Grind_proveEq_x3f___lam__0(v_lhs_1495_, v_rhs_1496_, v_abstract_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
stack->m_obj
 = v_res_1576_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(lean_object* v_lhs_1577_, lean_object* v_rhs_1578_, lean_object* v_abstract_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_abstract_boxed_1591_; lean_object* v_res_1592_; 
v_abstract_boxed_1591_ = lean_unbox(v_abstract_1579_);
v_res_1592_ = l_Lean_Meta_Grind_proveEq_x3f___lam__0(v_lhs_1577_, v_rhs_1578_, v_abstract_boxed_1591_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec(v___y_1580_);
return v_res_1592_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Meta_Grind_proveEq_x3f___closed__0));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object* v_lhs_1596_, lean_object* v_rhs_1597_, uint8_t v_abstract_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_toCold_1610_; lean_object* v_options_1611_; lean_object* v_inheritedTraceOptions_1612_; uint8_t v_hasTrace_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; 
v_toCold_1610_ = lean_ctor_get(v_a_1607_, 0);
v_options_1611_ = lean_ctor_get(v_toCold_1610_, 2);
v_inheritedTraceOptions_1612_ = lean_ctor_get(v_toCold_1610_, 11);
v_hasTrace_1613_ = lean_ctor_get_uint8(v_options_1611_, sizeof(void*)*1);
v___x_1614_ = lean_box(v_abstract_1598_);
lean_inc_ref(v_rhs_1597_);
lean_inc_ref(v_lhs_1596_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed), 14, 3);
lean_closure_set(v___f_1615_, 0, v_lhs_1596_);
lean_closure_set(v___f_1615_, 1, v_rhs_1597_);
lean_closure_set(v___f_1615_, 2, v___x_1614_);
if (v_hasTrace_1613_ == 0)
{
v___y_1679_ = v_a_1599_;
v___y_1680_ = v_a_1600_;
v___y_1681_ = v_a_1601_;
v___y_1682_ = v_a_1602_;
v___y_1683_ = v_a_1603_;
v___y_1684_ = v_a_1604_;
v___y_1685_ = v_a_1605_;
v___y_1686_ = v_a_1606_;
v___y_1687_ = v_a_1607_;
v___y_1688_ = v_a_1608_;
goto v___jp_1678_;
}
else
{
lean_object* v_cls_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_cls_1712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1612_, v_options_1611_, v___x_1713_);
if (v___x_1714_ == 0)
{
v___y_1679_ = v_a_1599_;
v___y_1680_ = v_a_1600_;
v___y_1681_ = v_a_1601_;
v___y_1682_ = v_a_1602_;
v___y_1683_ = v_a_1603_;
v___y_1684_ = v_a_1604_;
v___y_1685_ = v_a_1605_;
v___y_1686_ = v_a_1606_;
v___y_1687_ = v_a_1607_;
v___y_1688_ = v_a_1608_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1715_ = lean_obj_once(&l_Lean_Meta_Grind_proveEq_x3f___closed__1, &l_Lean_Meta_Grind_proveEq_x3f___closed__1_once, _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1);
lean_inc_ref(v_lhs_1596_);
v___x_1716_ = l_Lean_MessageData_ofExpr(v_lhs_1596_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
lean_inc_ref(v_rhs_1597_);
v___x_1720_ = l_Lean_MessageData_ofExpr(v_rhs_1597_);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1712_, v___x_1723_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_dec_ref_known(v___x_1724_, 1);
v___y_1679_ = v_a_1599_;
v___y_1680_ = v_a_1600_;
v___y_1681_ = v_a_1601_;
v___y_1682_ = v_a_1602_;
v___y_1683_ = v_a_1603_;
v___y_1684_ = v_a_1604_;
v___y_1685_ = v_a_1605_;
v___y_1686_ = v_a_1606_;
v___y_1687_ = v_a_1607_;
v___y_1688_ = v_a_1608_;
goto v___jp_1678_;
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v___f_1615_);
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
v___jp_1616_:
{
if (lean_obj_tag(v___y_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___y_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___y_1627_, 1);
v___x_1629_ = lean_unbox(v_a_1628_);
lean_dec(v_a_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v___x_1630_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1615_, v___y_1626_, v___y_1621_, v___y_1624_, v___y_1625_, v___y_1617_, v___y_1620_, v___y_1618_, v___y_1622_, v___y_1619_, v___y_1623_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; 
lean_dec_ref(v___f_1615_);
v___x_1631_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1596_, v_rhs_1597_, v___y_1626_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1661_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1661_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1661_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_unbox(v_a_1632_);
lean_dec(v_a_1632_);
if (v___x_1636_ == 0)
{
if (v_abstract_1598_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v___x_1637_ = lean_box(0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1637_);
v___x_1639_ = v___x_1634_;
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
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_del_object(v___x_1634_);
v___x_1641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 13, 2);
lean_closure_set(v___x_1641_, 0, v_lhs_1596_);
lean_closure_set(v___x_1641_, 1, v_rhs_1597_);
v___x_1642_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___x_1641_, v___y_1626_, v___y_1621_, v___y_1624_, v___y_1625_, v___y_1617_, v___y_1620_, v___y_1618_, v___y_1622_, v___y_1619_, v___y_1623_);
return v___x_1642_;
}
}
else
{
lean_object* v___x_1643_; 
lean_del_object(v___x_1634_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1619_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1618_);
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1617_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1621_);
lean_inc(v___y_1626_);
v___x_1643_ = lean_grind_mk_eq_proof(v_lhs_1596_, v_rhs_1597_, v___y_1626_, v___y_1621_, v___y_1624_, v___y_1625_, v___y_1617_, v___y_1620_, v___y_1618_, v___y_1622_, v___y_1619_, v___y_1623_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1652_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1652_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1652_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_a_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1648_);
v___x_1650_ = v___x_1646_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1643_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1643_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v_a_1662_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1631_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1631_);
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
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v___f_1615_);
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v_a_1670_ = lean_ctor_get(v___y_1627_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___y_1627_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___y_1627_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___y_1627_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
v___jp_1678_:
{
lean_object* v___x_1689_; 
lean_inc_ref(v_rhs_1597_);
lean_inc_ref(v_lhs_1596_);
v___x_1689_ = l_Lean_Meta_Grind_hasSameType(v_lhs_1596_, v_rhs_1597_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1703_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec_ref(v___f_1615_);
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v___x_1695_ = lean_box(0);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1695_);
v___x_1697_ = v___x_1692_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1699_; 
lean_del_object(v___x_1692_);
v___x_1699_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1596_, v___y_1679_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; uint8_t v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v___x_1701_ = lean_unbox(v_a_1700_);
if (v___x_1701_ == 0)
{
v___y_1617_ = v___y_1683_;
v___y_1618_ = v___y_1685_;
v___y_1619_ = v___y_1687_;
v___y_1620_ = v___y_1684_;
v___y_1621_ = v___y_1680_;
v___y_1622_ = v___y_1686_;
v___y_1623_ = v___y_1688_;
v___y_1624_ = v___y_1681_;
v___y_1625_ = v___y_1682_;
v___y_1626_ = v___y_1679_;
v___y_1627_ = v___x_1699_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1702_; 
lean_dec_ref_known(v___x_1699_, 1);
v___x_1702_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1597_, v___y_1679_);
v___y_1617_ = v___y_1683_;
v___y_1618_ = v___y_1685_;
v___y_1619_ = v___y_1687_;
v___y_1620_ = v___y_1684_;
v___y_1621_ = v___y_1680_;
v___y_1622_ = v___y_1686_;
v___y_1623_ = v___y_1688_;
v___y_1624_ = v___y_1681_;
v___y_1625_ = v___y_1682_;
v___y_1626_ = v___y_1679_;
v___y_1627_ = v___x_1702_;
goto v___jp_1616_;
}
}
else
{
v___y_1617_ = v___y_1683_;
v___y_1618_ = v___y_1685_;
v___y_1619_ = v___y_1687_;
v___y_1620_ = v___y_1684_;
v___y_1621_ = v___y_1680_;
v___y_1622_ = v___y_1686_;
v___y_1623_ = v___y_1688_;
v___y_1624_ = v___y_1681_;
v___y_1625_ = v___y_1682_;
v___y_1626_ = v___y_1679_;
v___y_1627_ = v___x_1699_;
goto v___jp_1616_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec_ref(v___f_1615_);
lean_dec_ref(v_rhs_1597_);
lean_dec_ref(v_lhs_1596_);
v_a_1704_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1689_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1689_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_proveEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1596_ = stack[0].m_obj;
lean_object* v_rhs_1597_ = stack[1].m_obj;
uint8_t v_abstract_1598_ = stack[2].m_num;
lean_object* v_a_1599_ = stack[3].m_obj;
lean_object* v_a_1600_ = stack[4].m_obj;
lean_object* v_a_1601_ = stack[5].m_obj;
lean_object* v_a_1602_ = stack[6].m_obj;
lean_object* v_a_1603_ = stack[7].m_obj;
lean_object* v_a_1604_ = stack[8].m_obj;
lean_object* v_a_1605_ = stack[9].m_obj;
lean_object* v_a_1606_ = stack[10].m_obj;
lean_object* v_a_1607_ = stack[11].m_obj;
lean_object* v_a_1608_ = stack[12].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l_Lean_Meta_Grind_proveEq_x3f(v_lhs_1596_, v_rhs_1597_, v_abstract_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object* v_lhs_1734_, lean_object* v_rhs_1735_, lean_object* v_abstract_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
uint8_t v_abstract_boxed_1748_; lean_object* v_res_1749_; 
v_abstract_boxed_1748_ = lean_unbox(v_abstract_1736_);
v_res_1749_ = l_Lean_Meta_Grind_proveEq_x3f(v_lhs_1734_, v_rhs_1735_, v_abstract_boxed_1748_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec(v_a_1737_);
return v_res_1749_;
}
}
lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object* v_lhs_1750_, lean_object* v_rhs_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1750_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1756_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc(v___y_1752_);
v___x_1767_ = lean_grind_process_to_do(v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1764_, v_a_1766_, v___y_1752_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1796_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1796_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1796_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_unbox(v_a_1769_);
lean_dec(v_a_1769_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v___x_1774_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
else
{
lean_object* v___x_1778_; 
lean_del_object(v___x_1771_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1756_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc(v___y_1752_);
v___x_1778_ = lean_grind_mk_heq_proof(v_a_1764_, v_a_1766_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1787_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1787_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1787_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_a_1779_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1783_);
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_a_1788_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1778_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1797_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1768_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1768_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1805_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1767_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1767_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_a_1764_);
v_a_1813_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1765_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1765_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec_ref(v_rhs_1751_);
v_a_1821_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1763_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1763_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_proveHEq_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1750_ = stack[0].m_obj;
lean_object* v_rhs_1751_ = stack[1].m_obj;
lean_object* v___y_1752_ = stack[2].m_obj;
lean_object* v___y_1753_ = stack[3].m_obj;
lean_object* v___y_1754_ = stack[4].m_obj;
lean_object* v___y_1755_ = stack[5].m_obj;
lean_object* v___y_1756_ = stack[6].m_obj;
lean_object* v___y_1757_ = stack[7].m_obj;
lean_object* v___y_1758_ = stack[8].m_obj;
lean_object* v___y_1759_ = stack[9].m_obj;
lean_object* v___y_1760_ = stack[10].m_obj;
lean_object* v___y_1761_ = stack[11].m_obj;
lean_object* v_res_1829_;
v_res_1829_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(v_lhs_1750_, v_rhs_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
stack->m_obj
 = v_res_1829_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object* v_lhs_1830_, lean_object* v_rhs_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(v_lhs_1830_, v_rhs_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec(v___y_1832_);
return v_res_1843_;
}
}
lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object* v_lhs_1844_, lean_object* v_rhs_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___f_1857_; lean_object* v___y_1859_; lean_object* v___x_1908_; 
lean_inc_ref(v_rhs_1845_);
lean_inc_ref(v_lhs_1844_);
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1857_, 0, v_lhs_1844_);
lean_closure_set(v___f_1857_, 1, v_rhs_1845_);
v___x_1908_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1844_, v_a_1846_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; uint8_t v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v___x_1910_ = lean_unbox(v_a_1909_);
if (v___x_1910_ == 0)
{
v___y_1859_ = v___x_1908_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1911_; 
lean_dec_ref_known(v___x_1908_, 1);
v___x_1911_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1845_, v_a_1846_);
v___y_1859_ = v___x_1911_;
goto v___jp_1858_;
}
}
else
{
v___y_1859_ = v___x_1908_;
goto v___jp_1858_;
}
v___jp_1858_:
{
if (lean_obj_tag(v___y_1859_) == 0)
{
lean_object* v_a_1860_; uint8_t v___x_1861_; 
v_a_1860_ = lean_ctor_get(v___y_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___y_1859_, 1);
v___x_1861_ = lean_unbox(v_a_1860_);
lean_dec(v_a_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_rhs_1845_);
lean_dec_ref(v_lhs_1844_);
v___x_1862_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1857_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; 
lean_dec_ref(v___f_1857_);
v___x_1863_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1844_, v_rhs_1845_, v_a_1846_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1891_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1891_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1891_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_unbox(v_a_1864_);
lean_dec(v_a_1864_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec_ref(v_rhs_1845_);
lean_dec_ref(v_lhs_1844_);
v___x_1869_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1869_);
v___x_1871_ = v___x_1866_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
else
{
lean_object* v___x_1873_; 
lean_del_object(v___x_1866_);
lean_inc(v_a_1855_);
lean_inc_ref(v_a_1854_);
lean_inc(v_a_1853_);
lean_inc_ref(v_a_1852_);
lean_inc(v_a_1851_);
lean_inc_ref(v_a_1850_);
lean_inc(v_a_1849_);
lean_inc_ref(v_a_1848_);
lean_inc(v_a_1847_);
lean_inc(v_a_1846_);
v___x_1873_ = lean_grind_mk_heq_proof(v_lhs_1844_, v_rhs_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1883_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1873_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1873_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_rhs_1845_);
lean_dec_ref(v_lhs_1844_);
v_a_1892_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1863_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1863_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___f_1857_);
lean_dec_ref(v_rhs_1845_);
lean_dec_ref(v_lhs_1844_);
v_a_1900_ = lean_ctor_get(v___y_1859_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___y_1859_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___y_1859_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___y_1859_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_proveHEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1844_ = stack[0].m_obj;
lean_object* v_rhs_1845_ = stack[1].m_obj;
lean_object* v_a_1846_ = stack[2].m_obj;
lean_object* v_a_1847_ = stack[3].m_obj;
lean_object* v_a_1848_ = stack[4].m_obj;
lean_object* v_a_1849_ = stack[5].m_obj;
lean_object* v_a_1850_ = stack[6].m_obj;
lean_object* v_a_1851_ = stack[7].m_obj;
lean_object* v_a_1852_ = stack[8].m_obj;
lean_object* v_a_1853_ = stack[9].m_obj;
lean_object* v_a_1854_ = stack[10].m_obj;
lean_object* v_a_1855_ = stack[11].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l_Lean_Meta_Grind_proveHEq_x3f(v_lhs_1844_, v_rhs_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object* v_lhs_1913_, lean_object* v_rhs_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Meta_Grind_proveHEq_x3f(v_lhs_1913_, v_rhs_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec(v_a_1915_);
return v_res_1926_;
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
