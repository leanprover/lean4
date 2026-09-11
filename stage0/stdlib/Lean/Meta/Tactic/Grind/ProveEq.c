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
lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___x_517_; 
v___x_517_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_877_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_877_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_877_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_877_;
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
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_876_; 
v_val_526_ = lean_ctor_get(v_a_518_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_876_ == 0)
{
v___x_528_ = v_a_518_;
v_isShared_529_ = v_isSharedCheck_876_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_a_518_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_876_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_875_; 
v_fst_530_ = lean_ctor_get(v_val_526_, 0);
v_snd_531_ = lean_ctor_get(v_val_526_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_val_526_);
if (v_isSharedCheck_875_ == 0)
{
v___x_533_ = v_val_526_;
v_isShared_534_ = v_isSharedCheck_875_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
lean_dec(v_val_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_875_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; uint8_t v___x_781_; 
v___x_781_ = lean_unbox(v_fst_530_);
lean_dec(v_fst_530_);
if (v___x_781_ == 0)
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
uint8_t v___x_782_; 
v___x_782_ = l_Lean_Expr_hasLooseBVars(v_lhs_454_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_Expr_hasLooseBVars(v_rhs_455_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_inc_ref(v_lhs_454_);
v___x_784_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_454_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
lean_inc_ref(v_rhs_455_);
v___x_786_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_455_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
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
v___x_788_ = lean_grind_process_new_facts(v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; 
lean_dec_ref_known(v___x_788_, 1);
v___x_789_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_785_, v_a_787_, v_a_458_);
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
lean_dec(v_a_787_);
lean_dec(v_a_785_);
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
lean_object* v___x_792_; 
lean_inc(v_a_787_);
lean_inc(v_a_785_);
v___x_792_ = l_Lean_Meta_Grind_hasSameType(v_a_785_, v_a_787_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; uint8_t v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = lean_unbox(v_a_793_);
lean_dec(v_a_793_);
if (v___x_794_ == 0)
{
lean_dec(v_a_787_);
lean_dec(v_a_785_);
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
lean_object* v___x_795_; 
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
lean_inc(v_a_785_);
v___x_795_ = lean_infer_type(v_a_785_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_826_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_826_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_826_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_826_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_cache_800_; lean_object* v_varTypes_801_; lean_object* v_lhss_802_; lean_object* v_rhss_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_825_; 
v_cache_800_ = lean_ctor_get(v_snd_531_, 0);
v_varTypes_801_ = lean_ctor_get(v_snd_531_, 1);
v_lhss_802_ = lean_ctor_get(v_snd_531_, 2);
v_rhss_803_ = lean_ctor_get(v_snd_531_, 3);
v_isSharedCheck_825_ = !lean_is_exclusive(v_snd_531_);
if (v_isSharedCheck_825_ == 0)
{
v___x_805_ = v_snd_531_;
v_isShared_806_ = v_isSharedCheck_825_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_rhss_803_);
lean_inc(v_lhss_802_);
lean_inc(v_varTypes_801_);
lean_inc(v_cache_800_);
lean_dec(v_snd_531_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_825_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_807_ = lean_array_get_size(v_varTypes_801_);
v___x_808_ = lean_nat_add(v___x_807_, v_a_456_);
v___x_809_ = lean_array_push(v_varTypes_801_, v_a_796_);
v___x_810_ = lean_array_push(v_lhss_802_, v_a_785_);
v___x_811_ = lean_array_push(v_rhss_803_, v_a_787_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 3, v___x_811_);
lean_ctor_set(v___x_805_, 2, v___x_810_);
lean_ctor_set(v___x_805_, 1, v___x_809_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_cache_800_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v___x_811_);
v___x_813_ = v_reuseFailAlloc_824_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = l_Lean_mkBVar(v___x_808_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_813_);
lean_ctor_set(v___x_533_, 0, v___x_814_);
v___x_816_ = v___x_533_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_813_);
v___x_816_ = v_reuseFailAlloc_823_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_816_);
v___x_818_ = v___x_528_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_818_);
v___x_820_ = v___x_798_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
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
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_787_);
lean_dec(v_a_785_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
v_a_827_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_795_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_795_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_787_);
lean_dec(v_a_785_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_835_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_792_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_792_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_787_);
lean_dec(v_a_785_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_843_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_789_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_789_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_a_787_);
lean_dec(v_a_785_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_851_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_788_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_788_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_a_785_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_859_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_786_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_786_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
lean_del_object(v___x_528_);
lean_del_object(v___x_520_);
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_867_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_784_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_784_);
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
}
else
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
}
else
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
v___y_470_ = v_typeName_765_;
v___y_471_ = v___y_536_;
v___y_472_ = v___y_537_;
v___y_473_ = v___y_539_;
v___y_474_ = v___y_542_;
v___y_475_ = v_struct_767_;
v___y_476_ = v_snd_531_;
v___y_477_ = v___y_538_;
v___y_478_ = v_idx_766_;
v___y_479_ = v___y_546_;
v___y_480_ = v___y_541_;
v___y_481_ = v_struct_770_;
v___y_482_ = v___y_544_;
v___y_483_ = v___y_545_;
v___y_484_ = v___y_540_;
v___y_485_ = v___y_543_;
v___y_486_ = v___x_771_;
goto v___jp_469_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_eq(v_idx_766_, v_idx_769_);
lean_dec(v_idx_769_);
v___y_470_ = v_typeName_765_;
v___y_471_ = v___y_536_;
v___y_472_ = v___y_537_;
v___y_473_ = v___y_539_;
v___y_474_ = v___y_542_;
v___y_475_ = v_struct_767_;
v___y_476_ = v_snd_531_;
v___y_477_ = v___y_538_;
v___y_478_ = v_idx_766_;
v___y_479_ = v___y_546_;
v___y_480_ = v___y_541_;
v___y_481_ = v_struct_770_;
v___y_482_ = v___y_544_;
v___y_483_ = v___y_545_;
v___y_484_ = v___y_540_;
v___y_485_ = v___y_543_;
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
}
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_rhs_455_);
lean_dec_ref(v_lhs_454_);
v_a_878_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_517_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_517_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
v___jp_469_:
{
if (v___y_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v___y_481_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_470_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_475_, v___y_481_, v___y_471_, v___y_476_, v___y_472_, v___y_477_, v___y_473_, v___y_484_, v___y_480_, v___y_474_, v___y_485_, v___y_482_, v___y_483_, v___y_479_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
if (lean_obj_tag(v_a_490_) == 0)
{
lean_dec(v___y_478_);
lean_dec(v___y_470_);
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
v___x_503_ = l_Lean_Expr_proj___override(v___y_470_, v___y_478_, v_fst_498_);
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
lean_dec(v___y_478_);
lean_dec(v___y_470_);
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(lean_object* v_lhs_886_, lean_object* v_rhs_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
size_t v___x_901_; size_t v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_ptr_addr(v_lhs_886_);
v___x_902_ = lean_ptr_addr(v_rhs_887_);
v___x_903_ = lean_usize_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v_cache_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_cache_904_ = lean_ctor_get(v_a_889_, 0);
lean_inc_ref(v_rhs_887_);
lean_inc_ref(v_lhs_886_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_lhs_886_);
lean_ctor_set(v___x_905_, 1, v_rhs_887_);
v___x_906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_904_, v___x_905_);
if (lean_obj_tag(v___x_906_) == 1)
{
lean_object* v_val_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref_known(v___x_905_, 2);
lean_dec_ref(v_rhs_887_);
lean_dec_ref(v_lhs_886_);
v_val_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_916_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_val_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_val_907_);
lean_ctor_set(v___x_911_, 1, v_a_889_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_915_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v___x_906_);
v___x_917_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_886_, v_rhs_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
if (lean_obj_tag(v_a_918_) == 0)
{
lean_dec_ref_known(v___x_905_, 2);
return v___x_917_;
}
else
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_954_; 
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v___x_917_, 0);
lean_dec(v_unused_955_);
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_954_;
goto v_resetjp_919_;
}
else
{
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_954_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_val_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_953_; 
v_val_922_ = lean_ctor_get(v_a_918_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_918_);
if (v_isSharedCheck_953_ == 0)
{
v___x_924_ = v_a_918_;
v_isShared_925_ = v_isSharedCheck_953_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_val_922_);
lean_dec(v_a_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_953_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_snd_926_; lean_object* v_fst_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_952_; 
v_snd_926_ = lean_ctor_get(v_val_922_, 1);
v_fst_927_ = lean_ctor_get(v_val_922_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_val_922_);
if (v_isSharedCheck_952_ == 0)
{
v___x_929_ = v_val_922_;
v_isShared_930_ = v_isSharedCheck_952_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snd_926_);
lean_inc(v_fst_927_);
lean_dec(v_val_922_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_952_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_cache_931_; lean_object* v_varTypes_932_; lean_object* v_lhss_933_; lean_object* v_rhss_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_951_; 
v_cache_931_ = lean_ctor_get(v_snd_926_, 0);
v_varTypes_932_ = lean_ctor_get(v_snd_926_, 1);
v_lhss_933_ = lean_ctor_get(v_snd_926_, 2);
v_rhss_934_ = lean_ctor_get(v_snd_926_, 3);
v_isSharedCheck_951_ = !lean_is_exclusive(v_snd_926_);
if (v_isSharedCheck_951_ == 0)
{
v___x_936_ = v_snd_926_;
v_isShared_937_ = v_isSharedCheck_951_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_rhss_934_);
lean_inc(v_lhss_933_);
lean_inc(v_varTypes_932_);
lean_inc(v_cache_931_);
lean_dec(v_snd_926_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_951_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
lean_inc(v_fst_927_);
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_931_, v___x_905_, v_fst_927_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_varTypes_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_lhss_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_rhss_934_);
v___x_940_ = v_reuseFailAlloc_950_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_940_);
v___x_942_ = v___x_929_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_fst_927_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_940_);
v___x_942_ = v_reuseFailAlloc_949_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_942_);
v___x_944_ = v___x_924_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_944_);
v___x_946_ = v___x_920_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
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
lean_dec_ref_known(v___x_905_, 2);
return v___x_917_;
}
}
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v_rhs_887_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_lhs_886_);
lean_ctor_set(v___x_956_, 1, v_a_889_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(lean_object* v_00_u03b2_1012_, lean_object* v_a_1013_, lean_object* v_x_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_a_1017_, lean_object* v_x_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_1016_, v_a_1017_, v_x_1018_);
lean_dec(v_x_1018_);
lean_dec_ref(v_a_1017_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(lean_object* v_00_u03b2_1021_, lean_object* v_data_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_data_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(lean_object* v_00_u03b2_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_1025_, v_b_1026_, v_x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1029_, lean_object* v_i_1030_, lean_object* v_source_1031_, lean_object* v_target_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v_i_1030_, v_source_1031_, v_target_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1035_, v_x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_unsigned_to_nat(16u);
v___x_1040_ = lean_mk_array(v___x_1039_, v___x_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_1041_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2));
v___x_1047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
v___x_1048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_1046_);
lean_ctor_set(v___x_1048_, 2, v___x_1046_);
lean_ctor_set(v___x_1048_, 3, v___x_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(lean_object* v_lhs_1056_, lean_object* v_rhs_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_Sym_shareCommon(v_lhs_1056_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = l_Lean_Meta_Sym_shareCommon(v_rhs_1057_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
v___x_1075_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_1070_, v_a_1072_, v___x_1073_, v___x_1074_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1145_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1145_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1145_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
if (lean_obj_tag(v_a_1076_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1140_; 
v_val_1080_ = lean_ctor_get(v_a_1076_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_a_1076_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1082_ = v_a_1076_;
v_isShared_1083_ = v_isSharedCheck_1140_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_val_1080_);
lean_dec(v_a_1076_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1140_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_snd_1084_; lean_object* v_fst_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1139_; 
v_snd_1084_ = lean_ctor_get(v_val_1080_, 1);
v_fst_1085_ = lean_ctor_get(v_val_1080_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_val_1080_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1087_ = v_val_1080_;
v_isShared_1088_ = v_isSharedCheck_1139_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snd_1084_);
lean_inc(v_fst_1085_);
lean_dec(v_val_1080_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1139_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_varTypes_1089_; lean_object* v_lhss_1090_; lean_object* v_rhss_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_varTypes_1089_ = lean_ctor_get(v_snd_1084_, 1);
lean_inc_ref(v_varTypes_1089_);
v_lhss_1090_ = lean_ctor_get(v_snd_1084_, 2);
lean_inc_ref(v_lhss_1090_);
v_rhss_1091_ = lean_ctor_get(v_snd_1084_, 3);
lean_inc_ref(v_rhss_1091_);
lean_dec(v_snd_1084_);
v___x_1092_ = lean_array_get_size(v_lhss_1090_);
v___x_1093_ = lean_nat_dec_eq(v___x_1092_, v___x_1073_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_del_object(v___x_1078_);
v___x_1094_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_1089_, v_fst_1085_);
lean_dec_ref(v_varTypes_1089_);
lean_inc(v_a_1067_);
lean_inc_ref(v_a_1066_);
lean_inc(v_a_1065_);
lean_inc_ref(v_a_1064_);
lean_inc_ref(v___x_1094_);
v___x_1095_ = lean_infer_type(v___x_1094_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_n(v_a_1096_, 2);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_Meta_getLevel(v_a_1096_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1118_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1118_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1118_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7));
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_a_1098_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_Expr_const___override(v___x_1102_, v___x_1104_);
v___x_1106_ = l_Lean_mkAppB(v___x_1105_, v_a_1096_, v___x_1094_);
lean_inc_ref(v___x_1106_);
v___x_1107_ = l_Lean_mkAppN(v___x_1106_, v_lhss_1090_);
lean_dec_ref(v_lhss_1090_);
v___x_1108_ = l_Lean_mkAppN(v___x_1106_, v_rhss_1091_);
lean_dec_ref(v_rhss_1091_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v___x_1108_);
lean_ctor_set(v___x_1087_, 0, v___x_1107_);
v___x_1110_ = v___x_1087_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1110_);
v___x_1112_ = v___x_1082_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1112_);
v___x_1114_ = v___x_1100_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1096_);
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_rhss_1091_);
lean_dec_ref(v_lhss_1090_);
lean_del_object(v___x_1087_);
lean_del_object(v___x_1082_);
v_a_1119_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1097_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1097_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_rhss_1091_);
lean_dec_ref(v_lhss_1090_);
lean_del_object(v___x_1087_);
lean_del_object(v___x_1082_);
v_a_1127_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1095_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1095_);
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
lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_dec_ref(v_rhss_1091_);
lean_dec_ref(v_lhss_1090_);
lean_dec_ref(v_varTypes_1089_);
lean_del_object(v___x_1087_);
lean_dec(v_fst_1085_);
lean_del_object(v___x_1082_);
v___x_1135_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1135_);
v___x_1137_ = v___x_1078_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_a_1076_);
v___x_1141_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1141_);
v___x_1143_ = v___x_1078_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1146_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1075_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1075_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_a_1070_);
v_a_1154_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1071_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1071_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_rhs_1057_);
v_a_1162_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1069_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1069_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(lean_object* v_lhs_1170_, lean_object* v_rhs_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_1170_, v_rhs_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec(v_a_1172_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(lean_object* v_msgData_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v_toCold_1193_; lean_object* v_mctx_1194_; lean_object* v_lctx_1195_; lean_object* v_options_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1190_ = lean_st_ref_get(v___y_1188_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_st_ref_get(v___y_1186_);
v_toCold_1193_ = lean_ctor_get(v___y_1187_, 0);
v_mctx_1194_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_mctx_1194_);
lean_dec(v___x_1192_);
v_lctx_1195_ = lean_ctor_get(v___y_1185_, 2);
v_options_1196_ = lean_ctor_get(v_toCold_1193_, 2);
lean_inc_ref(v_options_1196_);
lean_inc_ref(v_lctx_1195_);
v___x_1197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1197_, 0, v_env_1191_);
lean_ctor_set(v___x_1197_, 1, v_mctx_1194_);
lean_ctor_set(v___x_1197_, 2, v_lctx_1195_);
lean_ctor_set(v___x_1197_, 3, v_options_1196_);
v___x_1198_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_msgData_1184_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(lean_object* v_msgData_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1207_; double v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_float_of_nat(v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(lean_object* v_cls_1212_, lean_object* v_msg_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_ref_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1265_; 
v_ref_1219_ = lean_ctor_get(v___y_1216_, 2);
v___x_1220_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1265_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1265_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v_traceState_1226_; lean_object* v_env_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_ngen_1229_; lean_object* v_auxDeclNGen_1230_; lean_object* v_cache_1231_; lean_object* v_messages_1232_; lean_object* v_infoState_1233_; lean_object* v_snapshotTasks_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1264_; 
v___x_1225_ = lean_st_ref_take(v___y_1217_);
v_traceState_1226_ = lean_ctor_get(v___x_1225_, 4);
v_env_1227_ = lean_ctor_get(v___x_1225_, 0);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1225_, 1);
v_ngen_1229_ = lean_ctor_get(v___x_1225_, 2);
v_auxDeclNGen_1230_ = lean_ctor_get(v___x_1225_, 3);
v_cache_1231_ = lean_ctor_get(v___x_1225_, 5);
v_messages_1232_ = lean_ctor_get(v___x_1225_, 6);
v_infoState_1233_ = lean_ctor_get(v___x_1225_, 7);
v_snapshotTasks_1234_ = lean_ctor_get(v___x_1225_, 8);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1236_ = v___x_1225_;
v_isShared_1237_ = v_isSharedCheck_1264_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snapshotTasks_1234_);
lean_inc(v_infoState_1233_);
lean_inc(v_messages_1232_);
lean_inc(v_cache_1231_);
lean_inc(v_traceState_1226_);
lean_inc(v_auxDeclNGen_1230_);
lean_inc(v_ngen_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_env_1227_);
lean_dec(v___x_1225_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1264_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
uint64_t v_tid_1238_; lean_object* v_traces_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1263_; 
v_tid_1238_ = lean_ctor_get_uint64(v_traceState_1226_, sizeof(void*)*1);
v_traces_1239_ = lean_ctor_get(v_traceState_1226_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_traceState_1226_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1241_ = v_traceState_1226_;
v_isShared_1242_ = v_isSharedCheck_1263_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_traces_1239_);
lean_dec(v_traceState_1226_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1263_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; double v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
v___x_1245_ = 0;
v___x_1246_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1));
v___x_1247_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1247_, 0, v_cls_1212_);
lean_ctor_set(v___x_1247_, 1, v___x_1243_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
lean_ctor_set_float(v___x_1247_, sizeof(void*)*3, v___x_1244_);
lean_ctor_set_float(v___x_1247_, sizeof(void*)*3 + 8, v___x_1244_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*3 + 16, v___x_1245_);
v___x_1248_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2));
v___x_1249_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v_a_1221_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
lean_inc(v_ref_1219_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_ref_1219_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_PersistentArray_push___redArg(v_traces_1239_, v___x_1250_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1251_);
v___x_1253_ = v___x_1241_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1251_);
lean_ctor_set_uint64(v_reuseFailAlloc_1262_, sizeof(void*)*1, v_tid_1238_);
v___x_1253_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 4, v___x_1253_);
v___x_1255_ = v___x_1236_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_env_1227_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_ngen_1229_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_auxDeclNGen_1230_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v_cache_1231_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v_messages_1232_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_infoState_1233_);
lean_ctor_set(v_reuseFailAlloc_1261_, 8, v_snapshotTasks_1234_);
v___x_1255_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = lean_st_ref_put(v___y_1217_, v___x_1255_);
v___x_1257_ = lean_box(0);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1257_);
v___x_1259_ = v___x_1223_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(lean_object* v_cls_1266_, lean_object* v_msg_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1266_, v_msg_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5));
v___x_1286_ = l_Lean_Name_append(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(lean_object* v_lhs_u2080_1296_, lean_object* v_rhs_u2080_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_1296_, v_rhs_u2080_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1435_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1435_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1435_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
if (lean_obj_tag(v_a_1310_) == 1)
{
lean_object* v_val_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1430_; 
lean_del_object(v___x_1312_);
v_val_1314_ = lean_ctor_get(v_a_1310_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_a_1310_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1316_ = v_a_1310_;
v_isShared_1317_ = v_isSharedCheck_1430_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_val_1314_);
lean_dec(v_a_1310_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1430_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_fst_1318_; lean_object* v_snd_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1429_; 
v_fst_1318_ = lean_ctor_get(v_val_1314_, 0);
v_snd_1319_ = lean_ctor_get(v_val_1314_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_val_1314_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1321_ = v_val_1314_;
v_isShared_1322_ = v_isSharedCheck_1429_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snd_1319_);
lean_inc(v_fst_1318_);
lean_dec(v_val_1314_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1429_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_toCold_1402_; lean_object* v_options_1403_; uint8_t v_hasTrace_1404_; 
v_toCold_1402_ = lean_ctor_get(v_a_1306_, 0);
v_options_1403_ = lean_ctor_get(v_toCold_1402_, 2);
v_hasTrace_1404_ = lean_ctor_get_uint8(v_options_1403_, sizeof(void*)*1);
if (v_hasTrace_1404_ == 0)
{
lean_del_object(v___x_1321_);
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
v___y_1328_ = v_a_1302_;
v___y_1329_ = v_a_1303_;
v___y_1330_ = v_a_1304_;
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
goto v___jp_1323_;
}
else
{
lean_object* v_inheritedTraceOptions_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_inheritedTraceOptions_1405_ = lean_ctor_get(v_toCold_1402_, 11);
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1405_, v_options_1403_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_del_object(v___x_1321_);
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
v___y_1328_ = v_a_1302_;
v___y_1329_ = v_a_1303_;
v___y_1330_ = v_a_1304_;
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
lean_inc(v_fst_1318_);
v___x_1410_ = l_Lean_MessageData_ofExpr(v_fst_1318_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 7);
lean_ctor_set(v___x_1321_, 1, v___x_1410_);
lean_ctor_set(v___x_1321_, 0, v___x_1409_);
v___x_1412_ = v___x_1321_;
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
lean_inc(v_snd_1319_);
v___x_1415_ = l_Lean_MessageData_ofExpr(v_snd_1319_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_1406_, v___x_1418_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_dec_ref_known(v___x_1419_, 1);
v___y_1324_ = v_a_1298_;
v___y_1325_ = v_a_1299_;
v___y_1326_ = v_a_1300_;
v___y_1327_ = v_a_1301_;
v___y_1328_ = v_a_1302_;
v___y_1329_ = v_a_1303_;
v___y_1330_ = v_a_1304_;
v___y_1331_ = v_a_1305_;
v___y_1332_ = v_a_1306_;
v___y_1333_ = v_a_1307_;
goto v___jp_1323_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_snd_1319_);
lean_dec(v_fst_1318_);
lean_del_object(v___x_1316_);
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
v___jp_1323_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_1318_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_1319_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1338_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc(v___y_1324_);
v___x_1338_ = lean_grind_process_new_facts(v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1338_, 1);
v___x_1339_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1335_, v_a_1337_, v___y_1324_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1369_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1369_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1369_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_unbox(v_a_1340_);
lean_dec(v_a_1340_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec(v_a_1337_);
lean_dec(v_a_1335_);
lean_del_object(v___x_1316_);
v___x_1345_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
else
{
lean_object* v___x_1349_; 
lean_del_object(v___x_1342_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc(v___y_1324_);
v___x_1349_ = lean_grind_mk_eq_proof(v_a_1335_, v_a_1337_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1360_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_a_1350_);
v___x_1355_ = v___x_1316_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_del_object(v___x_1316_);
v_a_1361_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1349_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1349_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1337_);
lean_dec(v_a_1335_);
lean_del_object(v___x_1316_);
v_a_1370_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1339_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1339_);
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
lean_dec(v_a_1337_);
lean_dec(v_a_1335_);
lean_del_object(v___x_1316_);
v_a_1378_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1338_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1338_);
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
lean_dec(v_a_1335_);
lean_del_object(v___x_1316_);
v_a_1386_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1336_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1336_);
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
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_snd_1319_);
lean_del_object(v___x_1316_);
v_a_1394_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1334_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1334_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
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
lean_dec(v_a_1310_);
v___x_1431_ = lean_box(0);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1431_);
v___x_1433_ = v___x_1312_;
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
v_a_1436_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1309_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1309_);
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
lean_object* v_toCold_1600_; lean_object* v_options_1601_; lean_object* v_inheritedTraceOptions_1602_; uint8_t v_hasTrace_1603_; lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; 
v_toCold_1600_ = lean_ctor_get(v_a_1597_, 0);
v_options_1601_ = lean_ctor_get(v_toCold_1600_, 2);
v_inheritedTraceOptions_1602_ = lean_ctor_get(v_toCold_1600_, 11);
v_hasTrace_1603_ = lean_ctor_get_uint8(v_options_1601_, sizeof(void*)*1);
v___x_1604_ = lean_box(v_abstract_1588_);
lean_inc_ref(v_rhs_1587_);
lean_inc_ref(v_lhs_1586_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed), 14, 3);
lean_closure_set(v___f_1605_, 0, v_lhs_1586_);
lean_closure_set(v___f_1605_, 1, v_rhs_1587_);
lean_closure_set(v___f_1605_, 2, v___x_1604_);
if (v_hasTrace_1603_ == 0)
{
v___y_1669_ = v_a_1589_;
v___y_1670_ = v_a_1590_;
v___y_1671_ = v_a_1591_;
v___y_1672_ = v_a_1592_;
v___y_1673_ = v_a_1593_;
v___y_1674_ = v_a_1594_;
v___y_1675_ = v_a_1595_;
v___y_1676_ = v_a_1596_;
v___y_1677_ = v_a_1597_;
v___y_1678_ = v_a_1598_;
goto v___jp_1668_;
}
else
{
lean_object* v_cls_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_cls_1702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3));
v___x_1703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
v___x_1704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1602_, v_options_1601_, v___x_1703_);
if (v___x_1704_ == 0)
{
v___y_1669_ = v_a_1589_;
v___y_1670_ = v_a_1590_;
v___y_1671_ = v_a_1591_;
v___y_1672_ = v_a_1592_;
v___y_1673_ = v_a_1593_;
v___y_1674_ = v_a_1594_;
v___y_1675_ = v_a_1595_;
v___y_1676_ = v_a_1596_;
v___y_1677_ = v_a_1597_;
v___y_1678_ = v_a_1598_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1705_ = lean_obj_once(&l_Lean_Meta_Grind_proveEq_x3f___closed__1, &l_Lean_Meta_Grind_proveEq_x3f___closed__1_once, _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1);
lean_inc_ref(v_lhs_1586_);
v___x_1706_ = l_Lean_MessageData_ofExpr(v_lhs_1586_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
lean_inc_ref(v_rhs_1587_);
v___x_1710_ = l_Lean_MessageData_ofExpr(v_rhs_1587_);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12, &l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_1702_, v___x_1713_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_dec_ref_known(v___x_1714_, 1);
v___y_1669_ = v_a_1589_;
v___y_1670_ = v_a_1590_;
v___y_1671_ = v_a_1591_;
v___y_1672_ = v_a_1592_;
v___y_1673_ = v_a_1593_;
v___y_1674_ = v_a_1594_;
v___y_1675_ = v_a_1595_;
v___y_1676_ = v_a_1596_;
v___y_1677_ = v_a_1597_;
v___y_1678_ = v_a_1598_;
goto v___jp_1668_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v___f_1605_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
v___jp_1606_:
{
if (lean_obj_tag(v___y_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___y_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___y_1617_, 1);
v___x_1619_ = lean_unbox(v_a_1618_);
lean_dec(v_a_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v___x_1620_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1605_, v___y_1616_, v___y_1613_, v___y_1610_, v___y_1615_, v___y_1609_, v___y_1614_, v___y_1607_, v___y_1608_, v___y_1611_, v___y_1612_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; 
lean_dec_ref(v___f_1605_);
v___x_1621_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1586_, v_rhs_1587_, v___y_1616_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1651_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1651_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1651_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
uint8_t v___x_1626_; 
v___x_1626_ = lean_unbox(v_a_1622_);
lean_dec(v_a_1622_);
if (v___x_1626_ == 0)
{
if (v_abstract_1588_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v___x_1627_ = lean_box(0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_del_object(v___x_1624_);
v___x_1631_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed), 13, 2);
lean_closure_set(v___x_1631_, 0, v_lhs_1586_);
lean_closure_set(v___x_1631_, 1, v_rhs_1587_);
v___x_1632_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___x_1631_, v___y_1616_, v___y_1613_, v___y_1610_, v___y_1615_, v___y_1609_, v___y_1614_, v___y_1607_, v___y_1608_, v___y_1611_, v___y_1612_);
return v___x_1632_;
}
}
else
{
lean_object* v___x_1633_; 
lean_del_object(v___x_1624_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1609_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1613_);
lean_inc(v___y_1616_);
v___x_1633_ = lean_grind_mk_eq_proof(v_lhs_1586_, v_rhs_1587_, v___y_1616_, v___y_1613_, v___y_1610_, v___y_1615_, v___y_1609_, v___y_1614_, v___y_1607_, v___y_1608_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_a_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1633_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1633_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1652_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1621_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1621_);
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
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v___f_1605_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1660_ = lean_ctor_get(v___y_1617_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___y_1617_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___y_1617_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___y_1617_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
v___jp_1668_:
{
lean_object* v___x_1679_; 
lean_inc_ref(v_rhs_1587_);
lean_inc_ref(v_lhs_1586_);
v___x_1679_ = l_Lean_Meta_Grind_hasSameType(v_lhs_1586_, v_rhs_1587_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1693_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1693_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1693_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_unbox(v_a_1680_);
lean_dec(v_a_1680_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec_ref(v___f_1605_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v___x_1685_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1685_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
lean_object* v___x_1689_; 
lean_del_object(v___x_1682_);
v___x_1689_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1586_, v___y_1669_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; uint8_t v___x_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
v___x_1691_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
if (v___x_1691_ == 0)
{
v___y_1607_ = v___y_1675_;
v___y_1608_ = v___y_1676_;
v___y_1609_ = v___y_1673_;
v___y_1610_ = v___y_1671_;
v___y_1611_ = v___y_1677_;
v___y_1612_ = v___y_1678_;
v___y_1613_ = v___y_1670_;
v___y_1614_ = v___y_1674_;
v___y_1615_ = v___y_1672_;
v___y_1616_ = v___y_1669_;
v___y_1617_ = v___x_1689_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1692_; 
lean_dec_ref_known(v___x_1689_, 1);
v___x_1692_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1587_, v___y_1669_);
v___y_1607_ = v___y_1675_;
v___y_1608_ = v___y_1676_;
v___y_1609_ = v___y_1673_;
v___y_1610_ = v___y_1671_;
v___y_1611_ = v___y_1677_;
v___y_1612_ = v___y_1678_;
v___y_1613_ = v___y_1670_;
v___y_1614_ = v___y_1674_;
v___y_1615_ = v___y_1672_;
v___y_1616_ = v___y_1669_;
v___y_1617_ = v___x_1692_;
goto v___jp_1606_;
}
}
else
{
v___y_1607_ = v___y_1675_;
v___y_1608_ = v___y_1676_;
v___y_1609_ = v___y_1673_;
v___y_1610_ = v___y_1671_;
v___y_1611_ = v___y_1677_;
v___y_1612_ = v___y_1678_;
v___y_1613_ = v___y_1670_;
v___y_1614_ = v___y_1674_;
v___y_1615_ = v___y_1672_;
v___y_1616_ = v___y_1669_;
v___y_1617_ = v___x_1689_;
goto v___jp_1606_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v___f_1605_);
lean_dec_ref(v_rhs_1587_);
lean_dec_ref(v_lhs_1586_);
v_a_1694_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1679_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1679_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveEq_x3f___boxed(lean_object* v_lhs_1723_, lean_object* v_rhs_1724_, lean_object* v_abstract_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
uint8_t v_abstract_boxed_1737_; lean_object* v_res_1738_; 
v_abstract_boxed_1737_ = lean_unbox(v_abstract_1725_);
v_res_1738_ = l_Lean_Meta_Grind_proveEq_x3f(v_lhs_1723_, v_rhs_1724_, v_abstract_boxed_1737_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec(v_a_1726_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0(lean_object* v_lhs_1739_, lean_object* v_rhs_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_1739_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
lean_inc(v___y_1748_);
lean_inc_ref(v___y_1747_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1745_);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
lean_inc(v___y_1742_);
lean_inc(v___y_1741_);
v___x_1756_ = lean_grind_process_new_facts(v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref_known(v___x_1756_, 1);
v___x_1757_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1753_, v_a_1755_, v___y_1741_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1785_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1785_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1785_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_unbox(v_a_1758_);
lean_dec(v_a_1758_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec(v_a_1755_);
lean_dec(v_a_1753_);
v___x_1763_ = lean_box(0);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1763_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v___x_1767_; 
lean_del_object(v___x_1760_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
lean_inc(v___y_1748_);
lean_inc_ref(v___y_1747_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1745_);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
lean_inc(v___y_1742_);
lean_inc(v___y_1741_);
v___x_1767_ = lean_grind_mk_heq_proof(v_a_1753_, v_a_1755_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1776_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1768_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1767_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1767_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_a_1755_);
lean_dec(v_a_1753_);
v_a_1786_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1757_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1757_);
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
lean_dec(v_a_1755_);
lean_dec(v_a_1753_);
v_a_1794_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1756_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1756_);
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
lean_dec(v_a_1753_);
v_a_1802_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1754_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1754_);
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
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec_ref(v_rhs_1740_);
v_a_1810_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1752_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1752_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(lean_object* v_lhs_1818_, lean_object* v_rhs_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(v_lhs_1818_, v_rhs_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object* v_lhs_1832_, lean_object* v_rhs_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___f_1845_; lean_object* v___y_1847_; lean_object* v___x_1896_; 
lean_inc_ref(v_rhs_1833_);
lean_inc_ref(v_lhs_1832_);
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1845_, 0, v_lhs_1832_);
lean_closure_set(v___f_1845_, 1, v_rhs_1833_);
v___x_1896_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_1832_, v_a_1834_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; uint8_t v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
v___x_1898_ = lean_unbox(v_a_1897_);
lean_dec(v_a_1897_);
if (v___x_1898_ == 0)
{
v___y_1847_ = v___x_1896_;
goto v___jp_1846_;
}
else
{
lean_object* v___x_1899_; 
lean_dec_ref_known(v___x_1896_, 1);
v___x_1899_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_1833_, v_a_1834_);
v___y_1847_ = v___x_1899_;
goto v___jp_1846_;
}
}
else
{
v___y_1847_ = v___x_1896_;
goto v___jp_1846_;
}
v___jp_1846_:
{
if (lean_obj_tag(v___y_1847_) == 0)
{
lean_object* v_a_1848_; uint8_t v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___y_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___y_1847_, 1);
v___x_1849_ = lean_unbox(v_a_1848_);
lean_dec(v_a_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_dec_ref(v_rhs_1833_);
lean_dec_ref(v_lhs_1832_);
v___x_1850_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(v___f_1845_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; 
lean_dec_ref(v___f_1845_);
v___x_1851_ = l_Lean_Meta_Grind_isEqv___redArg(v_lhs_1832_, v_rhs_1833_, v_a_1834_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1879_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1879_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1879_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec_ref(v_rhs_1833_);
lean_dec_ref(v_lhs_1832_);
v___x_1857_ = lean_box(0);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v___x_1861_; 
lean_del_object(v___x_1854_);
lean_inc(v_a_1843_);
lean_inc_ref(v_a_1842_);
lean_inc(v_a_1841_);
lean_inc_ref(v_a_1840_);
lean_inc(v_a_1839_);
lean_inc_ref(v_a_1838_);
lean_inc(v_a_1837_);
lean_inc_ref(v_a_1836_);
lean_inc(v_a_1835_);
lean_inc(v_a_1834_);
v___x_1861_ = lean_grind_mk_heq_proof(v_lhs_1832_, v_rhs_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1870_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_a_1862_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1866_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_a_1871_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1861_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1861_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_rhs_1833_);
lean_dec_ref(v_lhs_1832_);
v_a_1880_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1851_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1851_);
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
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v___f_1845_);
lean_dec_ref(v_rhs_1833_);
lean_dec_ref(v_lhs_1832_);
v_a_1888_ = lean_ctor_get(v___y_1847_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___y_1847_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___y_1847_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___y_1847_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_proveHEq_x3f___boxed(lean_object* v_lhs_1900_, lean_object* v_rhs_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_Grind_proveHEq_x3f(v_lhs_1900_, v_rhs_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec(v_a_1902_);
return v_res_1913_;
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
