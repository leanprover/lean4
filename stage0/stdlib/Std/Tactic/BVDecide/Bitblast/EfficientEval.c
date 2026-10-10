// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.EfficientEval
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic import Init.System.IO import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr import Std.Data.HashMap.Basic
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t, uint8_t, uint8_t);
lean_object* l_runST___redArg(lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__0, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__0_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0(lean_object* v_x_7_, lean_object* v_assign_8_, lean_object* v_00_u03c3_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_12_ = lean_st_mk_ref(v___x_11_);
lean_inc(v___x_12_);
v___x_13_ = lean_apply_4(v_x_7_, lean_box(0), v_assign_8_, v___x_12_, lean_box(0));
v___x_14_ = lean_st_ref_get(v___x_12_);
lean_dec(v___x_12_);
lean_dec(v___x_14_);
return v___x_13_;
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_7_ = stack[0].m_obj;
lean_object* v_assign_8_ = stack[1].m_obj;
lean_object* v_res_15_;
v_res_15_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0(v_x_7_, v_assign_8_, lean_box(0));
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed(lean_object* v_x_16_, lean_object* v_assign_17_, lean_object* v_00_u03c3_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0(v_x_16_, v_assign_17_, v_00_u03c3_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg(lean_object* v_assign_21_, lean_object* v_x_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; 
v___f_23_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_23_, 0, v_x_22_);
lean_closure_set(v___f_23_, 1, v_assign_21_);
v___x_24_ = l_runST___redArg(v___f_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run(lean_object* v_00_u03b1_25_, lean_object* v_assign_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_28_, 0, v_x_27_);
lean_closure_set(v___f_28_, 1, v_assign_26_);
v___x_29_ = l_runST___redArg(v___f_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(lean_object* v_a_30_, lean_object* v_b_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_dec(v_b_31_);
lean_dec_ref(v_a_30_);
return v_x_32_;
}
else
{
lean_object* v_key_33_; lean_object* v_value_34_; lean_object* v_tail_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_47_; 
v_key_33_ = lean_ctor_get(v_x_32_, 0);
v_value_34_ = lean_ctor_get(v_x_32_, 1);
v_tail_35_ = lean_ctor_get(v_x_32_, 2);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_47_ == 0)
{
v___x_37_ = v_x_32_;
v_isShared_38_ = v_isSharedCheck_47_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_tail_35_);
lean_inc(v_value_34_);
lean_inc(v_key_33_);
lean_dec(v_x_32_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_47_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
uint8_t v___x_39_; 
v___x_39_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_key_33_, v_a_30_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(v_a_30_, v_b_31_, v_tail_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 2, v___x_40_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_key_33_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_value_34_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
else
{
lean_object* v___x_45_; 
lean_dec(v_value_34_);
lean_dec(v_key_33_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v_b_31_);
lean_ctor_set(v___x_37_, 0, v_a_30_);
v___x_45_ = v___x_37_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_30_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_b_31_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v_tail_35_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(lean_object* v_a_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
uint8_t v___x_50_; 
v___x_50_ = 0;
return v___x_50_;
}
else
{
lean_object* v_key_51_; lean_object* v_tail_52_; uint8_t v___x_53_; 
v_key_51_ = lean_ctor_get(v_x_49_, 0);
v_tail_52_ = lean_ctor_get(v_x_49_, 2);
v___x_53_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_key_51_, v_a_48_);
if (v___x_53_ == 0)
{
v_x_49_ = v_tail_52_;
goto _start;
}
else
{
return v___x_53_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_48_ = stack[0].m_obj;
lean_object* v_x_49_ = stack[1].m_obj;
uint8_t v_res_55_;
v_res_55_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_48_, v_x_49_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg___boxed(lean_object* v_a_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec_ref(v_a_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
return v_x_60_;
}
else
{
lean_object* v_key_62_; lean_object* v_value_63_; lean_object* v_tail_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_95_; 
v_key_62_ = lean_ctor_get(v_x_61_, 0);
v_value_63_ = lean_ctor_get(v_x_61_, 1);
v_tail_64_ = lean_ctor_get(v_x_61_, 2);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_61_);
if (v_isSharedCheck_95_ == 0)
{
v___x_66_ = v_x_61_;
v_isShared_67_ = v_isSharedCheck_95_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_tail_64_);
lean_inc(v_value_63_);
lean_inc(v_key_62_);
lean_dec(v_x_61_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_95_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_expr_68_; lean_object* v___x_69_; uint64_t v___y_71_; 
v_expr_68_ = lean_ctor_get(v_key_62_, 1);
v___x_69_ = lean_array_get_size(v_x_60_);
switch(lean_obj_tag(v_expr_68_))
{
case 0:
{
uint64_t v_hashCode_89_; 
v_hashCode_89_ = lean_ctor_get_uint64(v_expr_68_, sizeof(void*)*2);
v___y_71_ = v_hashCode_89_;
goto v___jp_70_;
}
case 1:
{
uint64_t v_hashCode_90_; 
v_hashCode_90_ = lean_ctor_get_uint64(v_expr_68_, sizeof(void*)*2);
v___y_71_ = v_hashCode_90_;
goto v___jp_70_;
}
case 3:
{
uint64_t v_hashCode_91_; 
v_hashCode_91_ = lean_ctor_get_uint64(v_expr_68_, sizeof(void*)*3);
v___y_71_ = v_hashCode_91_;
goto v___jp_70_;
}
case 4:
{
uint64_t v_hashCode_92_; 
v_hashCode_92_ = lean_ctor_get_uint64(v_expr_68_, sizeof(void*)*3);
v___y_71_ = v_hashCode_92_;
goto v___jp_70_;
}
case 5:
{
uint64_t v_hashCode_93_; 
v_hashCode_93_ = lean_ctor_get_uint64(v_expr_68_, sizeof(void*)*5);
v___y_71_ = v_hashCode_93_;
goto v___jp_70_;
}
default: 
{
uint64_t v_hashCode_94_; 
v_hashCode_94_ = lean_ctor_get_uint64(v_expr_68_, sizeof(void*)*4);
v___y_71_ = v_hashCode_94_;
goto v___jp_70_;
}
}
v___jp_70_:
{
uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v_fold_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_72_ = 32ULL;
v___x_73_ = lean_uint64_shift_right(v___y_71_, v___x_72_);
v_fold_74_ = lean_uint64_xor(v___y_71_, v___x_73_);
v___x_75_ = 16ULL;
v___x_76_ = lean_uint64_shift_right(v_fold_74_, v___x_75_);
v___x_77_ = lean_uint64_xor(v_fold_74_, v___x_76_);
v___x_78_ = lean_uint64_to_usize(v___x_77_);
v___x_79_ = lean_usize_of_nat(v___x_69_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_sub(v___x_79_, v___x_80_);
v___x_82_ = lean_usize_land(v___x_78_, v___x_81_);
v___x_83_ = lean_array_uget_borrowed(v_x_60_, v___x_82_);
lean_inc(v___x_83_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 2, v___x_83_);
v___x_85_ = v___x_66_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_key_62_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_value_63_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v___x_83_);
v___x_85_ = v_reuseFailAlloc_88_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; 
v___x_86_ = lean_array_uset(v_x_60_, v___x_82_, v___x_85_);
v_x_60_ = v___x_86_;
v_x_61_ = v_tail_64_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(lean_object* v_i_96_, lean_object* v_source_97_, lean_object* v_target_98_){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_array_get_size(v_source_97_);
v___x_100_ = lean_nat_dec_lt(v_i_96_, v___x_99_);
if (v___x_100_ == 0)
{
lean_dec_ref(v_source_97_);
lean_dec(v_i_96_);
return v_target_98_;
}
else
{
lean_object* v_es_101_; lean_object* v___x_102_; lean_object* v_source_103_; lean_object* v_target_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_es_101_ = lean_array_fget(v_source_97_, v_i_96_);
v___x_102_ = lean_box(0);
v_source_103_ = lean_array_fset(v_source_97_, v_i_96_, v___x_102_);
v_target_104_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(v_target_98_, v_es_101_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_i_96_, v___x_105_);
lean_dec(v_i_96_);
v_i_96_ = v___x_106_;
v_source_97_ = v_source_103_;
v_target_98_ = v_target_104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(lean_object* v_data_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_nbuckets_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_109_ = lean_array_get_size(v_data_108_);
v___x_110_ = lean_unsigned_to_nat(2u);
v_nbuckets_111_ = lean_nat_mul(v___x_109_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_box(0);
v___x_114_ = lean_mk_array(v_nbuckets_111_, v___x_113_);
v___x_115_ = lean_array_propagate_mark(v_data_108_, v___x_114_);
v___x_116_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(v___x_112_, v_data_108_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(lean_object* v_m_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
lean_object* v_size_120_; lean_object* v_buckets_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_172_; 
v_size_120_ = lean_ctor_get(v_m_117_, 0);
v_buckets_121_ = lean_ctor_get(v_m_117_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_m_117_);
if (v_isSharedCheck_172_ == 0)
{
v___x_123_ = v_m_117_;
v_isShared_124_ = v_isSharedCheck_172_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_buckets_121_);
lean_inc(v_size_120_);
lean_dec(v_m_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_172_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_expr_125_; lean_object* v___x_126_; uint64_t v___y_128_; 
v_expr_125_ = lean_ctor_get(v_a_118_, 1);
v___x_126_ = lean_array_get_size(v_buckets_121_);
switch(lean_obj_tag(v_expr_125_))
{
case 0:
{
uint64_t v_hashCode_166_; 
v_hashCode_166_ = lean_ctor_get_uint64(v_expr_125_, sizeof(void*)*2);
v___y_128_ = v_hashCode_166_;
goto v___jp_127_;
}
case 1:
{
uint64_t v_hashCode_167_; 
v_hashCode_167_ = lean_ctor_get_uint64(v_expr_125_, sizeof(void*)*2);
v___y_128_ = v_hashCode_167_;
goto v___jp_127_;
}
case 3:
{
uint64_t v_hashCode_168_; 
v_hashCode_168_ = lean_ctor_get_uint64(v_expr_125_, sizeof(void*)*3);
v___y_128_ = v_hashCode_168_;
goto v___jp_127_;
}
case 4:
{
uint64_t v_hashCode_169_; 
v_hashCode_169_ = lean_ctor_get_uint64(v_expr_125_, sizeof(void*)*3);
v___y_128_ = v_hashCode_169_;
goto v___jp_127_;
}
case 5:
{
uint64_t v_hashCode_170_; 
v_hashCode_170_ = lean_ctor_get_uint64(v_expr_125_, sizeof(void*)*5);
v___y_128_ = v_hashCode_170_;
goto v___jp_127_;
}
default: 
{
uint64_t v_hashCode_171_; 
v_hashCode_171_ = lean_ctor_get_uint64(v_expr_125_, sizeof(void*)*4);
v___y_128_ = v_hashCode_171_;
goto v___jp_127_;
}
}
v___jp_127_:
{
uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v_fold_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v_bkt_140_; uint8_t v___x_141_; 
v___x_129_ = 32ULL;
v___x_130_ = lean_uint64_shift_right(v___y_128_, v___x_129_);
v_fold_131_ = lean_uint64_xor(v___y_128_, v___x_130_);
v___x_132_ = 16ULL;
v___x_133_ = lean_uint64_shift_right(v_fold_131_, v___x_132_);
v___x_134_ = lean_uint64_xor(v_fold_131_, v___x_133_);
v___x_135_ = lean_uint64_to_usize(v___x_134_);
v___x_136_ = lean_usize_of_nat(v___x_126_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_sub(v___x_136_, v___x_137_);
v___x_139_ = lean_usize_land(v___x_135_, v___x_138_);
v_bkt_140_ = lean_array_uget_borrowed(v_buckets_121_, v___x_139_);
v___x_141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_118_, v_bkt_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v_size_x27_143_; lean_object* v___x_144_; lean_object* v_buckets_x27_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v_size_x27_143_ = lean_nat_add(v_size_120_, v___x_142_);
lean_dec(v_size_120_);
lean_inc(v_bkt_140_);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v_a_118_);
lean_ctor_set(v___x_144_, 1, v_b_119_);
lean_ctor_set(v___x_144_, 2, v_bkt_140_);
v_buckets_x27_145_ = lean_array_uset(v_buckets_121_, v___x_139_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(4u);
v___x_147_ = lean_nat_mul(v_size_x27_143_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = lean_nat_div(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_array_get_size(v_buckets_x27_145_);
v___x_151_ = lean_nat_dec_le(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v_val_152_; lean_object* v___x_154_; 
v_val_152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(v_buckets_x27_145_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_val_152_);
lean_ctor_set(v___x_123_, 0, v_size_x27_143_);
v___x_154_ = v___x_123_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_val_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_157_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_buckets_x27_145_);
lean_ctor_set(v___x_123_, 0, v_size_x27_143_);
v___x_157_ = v___x_123_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_buckets_x27_145_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v___x_159_; lean_object* v_buckets_x27_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc(v_bkt_140_);
v___x_159_ = lean_box(0);
v_buckets_x27_160_ = lean_array_uset(v_buckets_121_, v___x_139_, v___x_159_);
v___x_161_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(v_a_118_, v_b_119_, v_bkt_140_);
v___x_162_ = lean_array_uset(v_buckets_x27_160_, v___x_139_, v___x_161_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_162_);
v___x_164_ = v___x_123_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_120_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_key_176_; lean_object* v_value_177_; lean_object* v_tail_178_; uint8_t v___x_179_; 
v_key_176_ = lean_ctor_get(v_x_174_, 0);
v_value_177_ = lean_ctor_get(v_x_174_, 1);
v_tail_178_ = lean_ctor_get(v_x_174_, 2);
v___x_179_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_key_176_, v_a_173_);
if (v___x_179_ == 0)
{
v_x_174_ = v_tail_178_;
goto _start;
}
else
{
lean_object* v___x_181_; 
lean_inc(v_value_177_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_value_177_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg___boxed(lean_object* v_a_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(v_a_182_, v_x_183_);
lean_dec(v_x_183_);
lean_dec_ref(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(lean_object* v_m_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_buckets_187_; lean_object* v_expr_188_; lean_object* v___x_189_; uint64_t v___y_191_; 
v_buckets_187_ = lean_ctor_get(v_m_185_, 1);
v_expr_188_ = lean_ctor_get(v_a_186_, 1);
v___x_189_ = lean_array_get_size(v_buckets_187_);
switch(lean_obj_tag(v_expr_188_))
{
case 0:
{
uint64_t v_hashCode_205_; 
v_hashCode_205_ = lean_ctor_get_uint64(v_expr_188_, sizeof(void*)*2);
v___y_191_ = v_hashCode_205_;
goto v___jp_190_;
}
case 1:
{
uint64_t v_hashCode_206_; 
v_hashCode_206_ = lean_ctor_get_uint64(v_expr_188_, sizeof(void*)*2);
v___y_191_ = v_hashCode_206_;
goto v___jp_190_;
}
case 3:
{
uint64_t v_hashCode_207_; 
v_hashCode_207_ = lean_ctor_get_uint64(v_expr_188_, sizeof(void*)*3);
v___y_191_ = v_hashCode_207_;
goto v___jp_190_;
}
case 4:
{
uint64_t v_hashCode_208_; 
v_hashCode_208_ = lean_ctor_get_uint64(v_expr_188_, sizeof(void*)*3);
v___y_191_ = v_hashCode_208_;
goto v___jp_190_;
}
case 5:
{
uint64_t v_hashCode_209_; 
v_hashCode_209_ = lean_ctor_get_uint64(v_expr_188_, sizeof(void*)*5);
v___y_191_ = v_hashCode_209_;
goto v___jp_190_;
}
default: 
{
uint64_t v_hashCode_210_; 
v_hashCode_210_ = lean_ctor_get_uint64(v_expr_188_, sizeof(void*)*4);
v___y_191_ = v_hashCode_210_;
goto v___jp_190_;
}
}
v___jp_190_:
{
uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v_fold_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_192_ = 32ULL;
v___x_193_ = lean_uint64_shift_right(v___y_191_, v___x_192_);
v_fold_194_ = lean_uint64_xor(v___y_191_, v___x_193_);
v___x_195_ = 16ULL;
v___x_196_ = lean_uint64_shift_right(v_fold_194_, v___x_195_);
v___x_197_ = lean_uint64_xor(v_fold_194_, v___x_196_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = lean_usize_of_nat(v___x_189_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_sub(v___x_199_, v___x_200_);
v___x_202_ = lean_usize_land(v___x_198_, v___x_201_);
v___x_203_ = lean_array_uget_borrowed(v_buckets_187_, v___x_202_);
v___x_204_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(v_a_186_, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg___boxed(lean_object* v_m_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(v_m_211_, v_a_212_);
lean_dec_ref(v_a_212_);
lean_dec_ref(v_m_211_);
return v_res_213_;
}
}
lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(lean_object* v_w_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
switch(lean_obj_tag(v_a_215_))
{
case 0:
{
lean_object* v_idx_219_; lean_object* v___x_220_; lean_object* v_w_221_; lean_object* v_bv_222_; uint8_t v___x_223_; 
v_idx_219_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_idx_219_);
lean_dec_ref_known(v_a_215_, 2);
lean_inc_ref(v_a_216_);
v___x_220_ = lean_apply_1(v_a_216_, v_idx_219_);
v_w_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_w_221_);
v_bv_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_bv_222_);
lean_dec_ref(v___x_220_);
v___x_223_ = lean_nat_dec_eq(v_w_221_, v_w_214_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
v___x_224_ = l_BitVec_setWidth(v_w_221_, v_w_214_, v_bv_222_);
lean_dec(v_bv_222_);
lean_dec(v_w_214_);
lean_dec(v_w_221_);
return v___x_224_;
}
else
{
lean_dec(v_w_221_);
lean_dec(v_w_214_);
return v_bv_222_;
}
}
case 1:
{
lean_object* v_val_225_; 
lean_dec(v_w_214_);
v_val_225_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_val_225_);
lean_dec_ref_known(v_a_215_, 2);
return v_val_225_;
}
case 2:
{
lean_object* v_w_226_; lean_object* v_start_227_; lean_object* v_expr_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_w_226_ = lean_ctor_get(v_a_215_, 0);
lean_inc(v_w_226_);
v_start_227_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_start_227_);
v_expr_228_ = lean_ctor_get(v_a_215_, 3);
lean_inc_ref(v_expr_228_);
lean_dec_ref_known(v_a_215_, 4);
v___x_229_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_226_, v_expr_228_, v_a_216_, v_a_217_);
v___x_230_ = l_BitVec_extractLsb_x27___redArg(v_start_227_, v_w_214_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v_w_214_);
lean_dec(v_start_227_);
return v___x_230_;
}
case 3:
{
lean_object* v_lhs_231_; uint8_t v_op_232_; lean_object* v_rhs_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_lhs_231_ = lean_ctor_get(v_a_215_, 1);
lean_inc_ref(v_lhs_231_);
v_op_232_ = lean_ctor_get_uint8(v_a_215_, sizeof(void*)*3 + 8);
v_rhs_233_ = lean_ctor_get(v_a_215_, 2);
lean_inc_ref(v_rhs_233_);
lean_dec_ref_known(v_a_215_, 3);
lean_inc_n(v_w_214_, 2);
v___x_234_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_214_, v_lhs_231_, v_a_216_, v_a_217_);
v___x_235_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_214_, v_rhs_233_, v_a_216_, v_a_217_);
v___x_236_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_214_, v_op_232_, v___x_234_, v___x_235_);
lean_dec(v___x_235_);
lean_dec(v___x_234_);
lean_dec(v_w_214_);
return v___x_236_;
}
case 4:
{
lean_object* v_op_237_; lean_object* v_operand_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_op_237_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_op_237_);
v_operand_238_ = lean_ctor_get(v_a_215_, 2);
lean_inc_ref(v_operand_238_);
lean_dec_ref_known(v_a_215_, 3);
lean_inc(v_w_214_);
v___x_239_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_214_, v_operand_238_, v_a_216_, v_a_217_);
v___x_240_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_214_, v_op_237_, v___x_239_);
lean_dec(v_op_237_);
return v___x_240_;
}
case 5:
{
lean_object* v_l_241_; lean_object* v_r_242_; lean_object* v_lhs_243_; lean_object* v_rhs_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_w_214_);
v_l_241_ = lean_ctor_get(v_a_215_, 0);
lean_inc(v_l_241_);
v_r_242_ = lean_ctor_get(v_a_215_, 1);
lean_inc_n(v_r_242_, 2);
v_lhs_243_ = lean_ctor_get(v_a_215_, 3);
lean_inc_ref(v_lhs_243_);
v_rhs_244_ = lean_ctor_get(v_a_215_, 4);
lean_inc_ref(v_rhs_244_);
lean_dec_ref_known(v_a_215_, 5);
v___x_245_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_l_241_, v_lhs_243_, v_a_216_, v_a_217_);
v___x_246_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_r_242_, v_rhs_244_, v_a_216_, v_a_217_);
v___x_247_ = l_BitVec_append___redArg(v_r_242_, v___x_245_, v___x_246_);
lean_dec(v___x_246_);
lean_dec(v___x_245_);
lean_dec(v_r_242_);
return v___x_247_;
}
case 6:
{
lean_object* v_w_248_; lean_object* v_n_249_; lean_object* v_expr_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_w_214_);
v_w_248_ = lean_ctor_get(v_a_215_, 0);
lean_inc_n(v_w_248_, 2);
v_n_249_ = lean_ctor_get(v_a_215_, 2);
lean_inc(v_n_249_);
v_expr_250_ = lean_ctor_get(v_a_215_, 3);
lean_inc_ref(v_expr_250_);
lean_dec_ref_known(v_a_215_, 4);
v___x_251_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_248_, v_expr_250_, v_a_216_, v_a_217_);
v___x_252_ = l_BitVec_replicate(v_w_248_, v_n_249_, v___x_251_);
lean_dec(v___x_251_);
lean_dec(v_n_249_);
lean_dec(v_w_248_);
return v___x_252_;
}
case 7:
{
lean_object* v_n_253_; lean_object* v_lhs_254_; lean_object* v_rhs_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_n_253_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_n_253_);
v_lhs_254_ = lean_ctor_get(v_a_215_, 2);
lean_inc_ref(v_lhs_254_);
v_rhs_255_ = lean_ctor_get(v_a_215_, 3);
lean_inc_ref(v_rhs_255_);
lean_dec_ref_known(v_a_215_, 4);
lean_inc(v_w_214_);
v___x_256_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_214_, v_lhs_254_, v_a_216_, v_a_217_);
v___x_257_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_n_253_, v_rhs_255_, v_a_216_, v_a_217_);
v___x_258_ = l_BitVec_shiftLeft(v_w_214_, v___x_256_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v___x_256_);
lean_dec(v_w_214_);
return v___x_258_;
}
case 8:
{
lean_object* v_n_259_; lean_object* v_lhs_260_; lean_object* v_rhs_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_n_259_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_n_259_);
v_lhs_260_ = lean_ctor_get(v_a_215_, 2);
lean_inc_ref(v_lhs_260_);
v_rhs_261_ = lean_ctor_get(v_a_215_, 3);
lean_inc_ref(v_rhs_261_);
lean_dec_ref_known(v_a_215_, 4);
v___x_262_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_214_, v_lhs_260_, v_a_216_, v_a_217_);
v___x_263_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_n_259_, v_rhs_261_, v_a_216_, v_a_217_);
v___x_264_ = lean_nat_shiftr(v___x_262_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v___x_262_);
return v___x_264_;
}
default: 
{
lean_object* v_n_265_; lean_object* v_lhs_266_; lean_object* v_rhs_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_n_265_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_n_265_);
v_lhs_266_ = lean_ctor_get(v_a_215_, 2);
lean_inc_ref(v_lhs_266_);
v_rhs_267_ = lean_ctor_get(v_a_215_, 3);
lean_inc_ref(v_rhs_267_);
lean_dec_ref_known(v_a_215_, 4);
lean_inc(v_w_214_);
v___x_268_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_214_, v_lhs_266_, v_a_216_, v_a_217_);
v___x_269_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_n_265_, v_rhs_267_, v_a_216_, v_a_217_);
v___x_270_ = l_BitVec_sshiftRight(v_w_214_, v___x_268_, v___x_269_);
lean_dec(v___x_269_);
lean_dec(v_w_214_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_214_ = stack[0].m_obj;
lean_object* v_a_215_ = stack[1].m_obj;
lean_object* v_a_216_ = stack[2].m_obj;
lean_object* v_a_217_ = stack[3].m_obj;
lean_object* v_res_271_;
v_res_271_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_214_, v_a_215_, v_a_216_, v_a_217_);
stack->m_obj
 = v_res_271_;
}
lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(lean_object* v_w_272_, lean_object* v_expr_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_key_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_inc_ref(v_expr_273_);
lean_inc(v_w_272_);
v_key_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_277_, 0, v_w_272_);
lean_ctor_set(v_key_277_, 1, v_expr_273_);
v___x_278_ = lean_st_ref_get(v_a_275_);
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(v___x_278_, v_key_277_);
lean_dec(v___x_278_);
if (lean_obj_tag(v___x_279_) == 1)
{
lean_object* v_val_280_; 
lean_dec_ref_known(v_key_277_, 2);
lean_dec_ref(v_expr_273_);
lean_dec(v_w_272_);
v_val_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v___x_279_, 1);
return v_val_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v___x_279_);
v___x_281_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_272_, v_expr_273_, v_a_274_, v_a_275_);
v___x_282_ = lean_st_ref_take(v_a_275_);
lean_inc(v___x_281_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(v___x_282_, v_key_277_, v___x_281_);
v___x_284_ = lean_st_ref_put(v_a_275_, v___x_283_);
return v___x_281_;
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_272_ = stack[0].m_obj;
lean_object* v_expr_273_ = stack[1].m_obj;
lean_object* v_a_274_ = stack[2].m_obj;
lean_object* v_a_275_ = stack[3].m_obj;
lean_object* v_res_285_;
v_res_285_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_272_, v_expr_273_, v_a_274_, v_a_275_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg___boxed(lean_object* v_w_286_, lean_object* v_expr_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_286_, v_expr_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg___boxed(lean_object* v_w_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_297_;
}
}
lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go(lean_object* v_00_u03c3_298_, lean_object* v_w_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_299_, v_a_300_, v_a_301_, v_a_302_);
return v___x_304_;
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_299_ = stack[1].m_obj;
lean_object* v_a_300_ = stack[2].m_obj;
lean_object* v_a_301_ = stack[3].m_obj;
lean_object* v_a_302_ = stack[4].m_obj;
lean_object* v_res_305_;
v_res_305_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go(lean_box(0), v_w_299_, v_a_300_, v_a_301_, v_a_302_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___boxed(lean_object* v_00_u03c3_306_, lean_object* v_w_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go(v_00_u03c3_306_, v_w_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v_res_312_;
}
}
lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM(lean_object* v_w_313_, lean_object* v_00_u03c3_314_, lean_object* v_expr_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_313_, v_expr_315_, v_a_316_, v_a_317_);
return v___x_319_;
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_313_ = stack[0].m_obj;
lean_object* v_expr_315_ = stack[2].m_obj;
lean_object* v_a_316_ = stack[3].m_obj;
lean_object* v_a_317_ = stack[4].m_obj;
lean_object* v_res_320_;
v_res_320_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM(v_w_313_, lean_box(0), v_expr_315_, v_a_316_, v_a_317_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___boxed(lean_object* v_w_321_, lean_object* v_00_u03c3_322_, lean_object* v_expr_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM(v_w_321_, v_00_u03c3_322_, v_expr_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1(lean_object* v_00_u03b2_328_, lean_object* v_inst_329_, lean_object* v_m_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(v_m_330_, v_a_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___boxed(lean_object* v_00_u03b2_333_, lean_object* v_inst_334_, lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1(v_00_u03b2_333_, v_inst_334_, v_m_335_, v_a_336_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_m_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2(lean_object* v_00_u03b2_338_, lean_object* v_m_339_, lean_object* v_a_340_, lean_object* v_b_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(v_m_339_, v_a_340_, v_b_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1(lean_object* v_00_u03b2_343_, lean_object* v_inst_344_, lean_object* v_a_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(v_a_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___boxed(lean_object* v_00_u03b2_348_, lean_object* v_inst_349_, lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1(v_00_u03b2_348_, v_inst_349_, v_a_350_, v_x_351_);
lean_dec(v_x_351_);
lean_dec_ref(v_a_350_);
return v_res_352_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3(lean_object* v_00_u03b2_353_, lean_object* v_a_354_, lean_object* v_x_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_354_ = stack[1].m_obj;
lean_object* v_x_355_ = stack[2].m_obj;
uint8_t v_res_357_;
v_res_357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3(lean_box(0), v_a_354_, v_x_355_);
stack->m_num = v_res_357_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___boxed(lean_object* v_00_u03b2_358_, lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3(v_00_u03b2_358_, v_a_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec_ref(v_a_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4(lean_object* v_00_u03b2_363_, lean_object* v_data_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(v_data_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5(lean_object* v_00_u03b2_366_, lean_object* v_a_367_, lean_object* v_b_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(v_a_367_, v_b_368_, v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_371_, lean_object* v_i_372_, lean_object* v_source_373_, lean_object* v_target_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(v_i_372_, v_source_373_, v_target_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(v_x_377_, v_x_378_);
return v___x_379_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(lean_object* v_expr_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
if (lean_obj_tag(v_expr_380_) == 0)
{
lean_object* v_w_384_; lean_object* v_lhs_385_; uint8_t v_op_386_; lean_object* v_rhs_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_w_384_ = lean_ctor_get(v_expr_380_, 0);
lean_inc_n(v_w_384_, 2);
v_lhs_385_ = lean_ctor_get(v_expr_380_, 1);
lean_inc_ref(v_lhs_385_);
v_op_386_ = lean_ctor_get_uint8(v_expr_380_, sizeof(void*)*3);
v_rhs_387_ = lean_ctor_get(v_expr_380_, 2);
lean_inc_ref(v_rhs_387_);
lean_dec_ref_known(v_expr_380_, 3);
v___x_388_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_384_, v_lhs_385_, v_a_381_, v_a_382_);
v___x_389_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_384_, v_rhs_387_, v_a_381_, v_a_382_);
v___x_390_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_386_, v___x_388_, v___x_389_);
lean_dec(v___x_389_);
lean_dec(v___x_388_);
return v___x_390_;
}
else
{
lean_object* v_w_391_; lean_object* v_expr_392_; lean_object* v_idx_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_w_391_ = lean_ctor_get(v_expr_380_, 0);
lean_inc(v_w_391_);
v_expr_392_ = lean_ctor_get(v_expr_380_, 1);
lean_inc_ref(v_expr_392_);
v_idx_393_ = lean_ctor_get(v_expr_380_, 2);
lean_inc(v_idx_393_);
lean_dec_ref_known(v_expr_380_, 3);
v___x_394_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_391_, v_expr_392_, v_a_381_, v_a_382_);
v___x_395_ = l_Nat_testBit(v___x_394_, v_idx_393_);
lean_dec(v_idx_393_);
lean_dec(v___x_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_380_ = stack[0].m_obj;
lean_object* v_a_381_ = stack[1].m_obj;
lean_object* v_a_382_ = stack[2].m_obj;
uint8_t v_res_396_;
v_res_396_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_380_, v_a_381_, v_a_382_);
stack->m_num = v_res_396_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg___boxed(lean_object* v_expr_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM(lean_object* v_00_u03c3_403_, lean_object* v_expr_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_404_, v_a_405_, v_a_406_);
return v___x_408_;
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_404_ = stack[1].m_obj;
lean_object* v_a_405_ = stack[2].m_obj;
lean_object* v_a_406_ = stack[3].m_obj;
uint8_t v_res_409_;
v_res_409_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM(lean_box(0), v_expr_404_, v_a_405_, v_a_406_);
stack->m_num = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___boxed(lean_object* v_00_u03c3_410_, lean_object* v_expr_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM(v_00_u03c3_410_, v_expr_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(lean_object* v_expr_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
switch(lean_obj_tag(v_expr_417_))
{
case 0:
{
lean_object* v_a_421_; uint8_t v___x_422_; 
v_a_421_ = lean_ctor_get(v_expr_417_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v_expr_417_, 1);
v___x_422_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_a_421_, v_a_418_, v_a_419_);
return v___x_422_;
}
case 1:
{
uint8_t v_a_423_; 
v_a_423_ = lean_ctor_get_uint8(v_expr_417_, 0);
lean_dec_ref_known(v_expr_417_, 0);
return v_a_423_;
}
case 2:
{
lean_object* v_a_424_; uint8_t v___x_425_; 
v_a_424_ = lean_ctor_get(v_expr_417_, 0);
lean_inc_ref(v_a_424_);
lean_dec_ref_known(v_expr_417_, 1);
v___x_425_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_424_, v_a_418_, v_a_419_);
if (v___x_425_ == 0)
{
uint8_t v___x_426_; 
v___x_426_ = 1;
return v___x_426_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
}
case 3:
{
uint8_t v_a_428_; lean_object* v_a_429_; lean_object* v_a_430_; uint8_t v___x_431_; uint8_t v___x_432_; uint8_t v___x_433_; 
v_a_428_ = lean_ctor_get_uint8(v_expr_417_, sizeof(void*)*2);
v_a_429_ = lean_ctor_get(v_expr_417_, 0);
lean_inc_ref(v_a_429_);
v_a_430_ = lean_ctor_get(v_expr_417_, 1);
lean_inc_ref(v_a_430_);
lean_dec_ref_known(v_expr_417_, 2);
v___x_431_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_429_, v_a_418_, v_a_419_);
v___x_432_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_430_, v_a_418_, v_a_419_);
v___x_433_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_428_, v___x_431_, v___x_432_);
return v___x_433_;
}
default: 
{
lean_object* v_a_434_; lean_object* v_a_435_; lean_object* v_a_436_; uint8_t v___x_437_; 
v_a_434_ = lean_ctor_get(v_expr_417_, 0);
lean_inc_ref(v_a_434_);
v_a_435_ = lean_ctor_get(v_expr_417_, 1);
lean_inc_ref(v_a_435_);
v_a_436_ = lean_ctor_get(v_expr_417_, 2);
lean_inc_ref(v_a_436_);
lean_dec_ref_known(v_expr_417_, 3);
v___x_437_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_434_, v_a_418_, v_a_419_);
if (v___x_437_ == 0)
{
lean_dec_ref(v_a_435_);
v_expr_417_ = v_a_436_;
goto _start;
}
else
{
lean_dec_ref(v_a_436_);
v_expr_417_ = v_a_435_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_417_ = stack[0].m_obj;
lean_object* v_a_418_ = stack[1].m_obj;
lean_object* v_a_419_ = stack[2].m_obj;
uint8_t v_res_440_;
v_res_440_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_417_, v_a_418_, v_a_419_);
stack->m_num = v_res_440_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg___boxed(lean_object* v_expr_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM(lean_object* v_00_u03c3_447_, lean_object* v_expr_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_448_, v_a_449_, v_a_450_);
return v___x_452_;
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_448_ = stack[1].m_obj;
lean_object* v_a_449_ = stack[2].m_obj;
lean_object* v_a_450_ = stack[3].m_obj;
uint8_t v_res_453_;
v_res_453_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM(lean_box(0), v_expr_448_, v_a_449_, v_a_450_);
stack->m_num = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___boxed(lean_object* v_00_u03c3_454_, lean_object* v_expr_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM(v_00_u03c3_454_, v_expr_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0(lean_object* v_w_461_, lean_object* v_expr_462_, lean_object* v_assign_463_, lean_object* v_00_u03c3_464_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_467_ = lean_st_mk_ref(v___x_466_);
v___x_468_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_461_, v_expr_462_, v_assign_463_, v___x_467_);
v___x_469_ = lean_st_ref_get(v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_469_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_461_ = stack[0].m_obj;
lean_object* v_expr_462_ = stack[1].m_obj;
lean_object* v_assign_463_ = stack[2].m_obj;
lean_object* v_res_470_;
v_res_470_ = l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0(v_w_461_, v_expr_462_, v_assign_463_, lean_box(0));
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0___boxed(lean_object* v_w_471_, lean_object* v_expr_472_, lean_object* v_assign_473_, lean_object* v_00_u03c3_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0(v_w_471_, v_expr_472_, v_assign_473_, v_00_u03c3_474_);
lean_dec_ref(v_assign_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient(lean_object* v_w_477_, lean_object* v_assign_478_, lean_object* v_expr_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; 
v___f_480_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0___boxed), 5, 3);
lean_closure_set(v___f_480_, 0, v_w_477_);
lean_closure_set(v___f_480_, 1, v_expr_479_);
lean_closure_set(v___f_480_, 2, v_assign_478_);
v___x_481_ = l_runST___redArg(v___f_480_);
return v___x_481_;
}
}
uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0(lean_object* v_expr_482_, lean_object* v_assign_483_, lean_object* v_00_u03c3_484_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_487_ = lean_st_mk_ref(v___x_486_);
v___x_488_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_482_, v_assign_483_, v___x_487_);
v___x_489_ = lean_st_ref_get(v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_489_);
return v___x_488_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_482_ = stack[0].m_obj;
lean_object* v_assign_483_ = stack[1].m_obj;
uint8_t v_res_490_;
v_res_490_ = l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0(v_expr_482_, v_assign_483_, lean_box(0));
stack->m_num = v_res_490_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0___boxed(lean_object* v_expr_491_, lean_object* v_assign_492_, lean_object* v_00_u03c3_493_, lean_object* v___y_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0(v_expr_491_, v_assign_492_, v_00_u03c3_493_);
lean_dec_ref(v_assign_492_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient(lean_object* v_assign_497_, lean_object* v_expr_498_){
_start:
{
lean_object* v___f_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___f_499_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0___boxed), 4, 2);
lean_closure_set(v___f_499_, 0, v_expr_498_);
lean_closure_set(v___f_499_, 1, v_assign_497_);
v___x_500_ = l_runST___redArg(v___f_499_);
v___x_501_ = lean_unbox(v___x_500_);
lean_dec(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_497_ = stack[0].m_obj;
lean_object* v_expr_498_ = stack[1].m_obj;
uint8_t v_res_502_;
v_res_502_ = l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient(v_assign_497_, v_expr_498_);
stack->m_num = v_res_502_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___boxed(lean_object* v_assign_503_, lean_object* v_expr_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient(v_assign_503_, v_expr_504_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0(lean_object* v_expr_507_, lean_object* v_assign_508_, lean_object* v_00_u03c3_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; 
v___x_511_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_512_ = lean_st_mk_ref(v___x_511_);
v___x_513_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_507_, v_assign_508_, v___x_512_);
v___x_514_ = lean_st_ref_get(v___x_512_);
lean_dec(v___x_512_);
lean_dec(v___x_514_);
return v___x_513_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_507_ = stack[0].m_obj;
lean_object* v_assign_508_ = stack[1].m_obj;
uint8_t v_res_515_;
v_res_515_ = l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0(v_expr_507_, v_assign_508_, lean_box(0));
stack->m_num = v_res_515_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0___boxed(lean_object* v_expr_516_, lean_object* v_assign_517_, lean_object* v_00_u03c3_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0(v_expr_516_, v_assign_517_, v_00_u03c3_518_);
lean_dec_ref(v_assign_517_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient(lean_object* v_assign_522_, lean_object* v_expr_523_){
_start:
{
lean_object* v___f_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___f_524_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0___boxed), 4, 2);
lean_closure_set(v___f_524_, 0, v_expr_523_);
lean_closure_set(v___f_524_, 1, v_assign_522_);
v___x_525_ = l_runST___redArg(v___f_524_);
v___x_526_ = lean_unbox(v___x_525_);
lean_dec(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_522_ = stack[0].m_obj;
lean_object* v_expr_523_ = stack[1].m_obj;
uint8_t v_res_527_;
v_res_527_ = l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient(v_assign_522_, v_expr_523_);
stack->m_num = v_res_527_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___boxed(lean_object* v_assign_528_, lean_object* v_expr_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient(v_assign_528_, v_expr_529_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_EfficientEval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_EfficientEval(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_EfficientEval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_EfficientEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_EfficientEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_EfficientEval(builtin);
}
#ifdef __cplusplus
}
#endif
