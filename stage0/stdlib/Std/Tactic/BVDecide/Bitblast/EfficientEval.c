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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0(lean_object* v_x_7_, lean_object* v_assign_8_, lean_object* v_00_u03c3_9_){
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v_assign_16_, lean_object* v_00_u03c3_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0(v_x_15_, v_assign_16_, v_00_u03c3_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg(lean_object* v_assign_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___f_22_; lean_object* v___x_23_; 
v___f_22_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_22_, 0, v_x_21_);
lean_closure_set(v___f_22_, 1, v_assign_20_);
v___x_23_ = l_runST___redArg(v___f_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run(lean_object* v_00_u03b1_24_, lean_object* v_assign_25_, lean_object* v_x_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; 
v___f_27_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_27_, 0, v_x_26_);
lean_closure_set(v___f_27_, 1, v_assign_25_);
v___x_28_ = l_runST___redArg(v___f_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(lean_object* v_a_29_, lean_object* v_b_30_, lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_dec(v_b_30_);
lean_dec_ref(v_a_29_);
return v_x_31_;
}
else
{
lean_object* v_key_32_; lean_object* v_value_33_; lean_object* v_tail_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_46_; 
v_key_32_ = lean_ctor_get(v_x_31_, 0);
v_value_33_ = lean_ctor_get(v_x_31_, 1);
v_tail_34_ = lean_ctor_get(v_x_31_, 2);
v_isSharedCheck_46_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_46_ == 0)
{
v___x_36_ = v_x_31_;
v_isShared_37_ = v_isSharedCheck_46_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_tail_34_);
lean_inc(v_value_33_);
lean_inc(v_key_32_);
lean_dec(v_x_31_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_46_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
uint8_t v___x_38_; 
v___x_38_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_key_32_, v_a_29_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_39_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(v_a_29_, v_b_30_, v_tail_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 2, v___x_39_);
v___x_41_ = v___x_36_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_key_32_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_value_33_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
else
{
lean_object* v___x_44_; 
lean_dec(v_value_33_);
lean_dec(v_key_32_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v_b_30_);
lean_ctor_set(v___x_36_, 0, v_a_29_);
v___x_44_ = v___x_36_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_29_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_b_30_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v_tail_34_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(lean_object* v_a_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
else
{
lean_object* v_key_50_; lean_object* v_tail_51_; uint8_t v___x_52_; 
v_key_50_ = lean_ctor_get(v_x_48_, 0);
v_tail_51_ = lean_ctor_get(v_x_48_, 2);
v___x_52_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_key_50_, v_a_47_);
if (v___x_52_ == 0)
{
v_x_48_ = v_tail_51_;
goto _start;
}
else
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg___boxed(lean_object* v_a_54_, lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec_ref(v_a_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
return v_x_58_;
}
else
{
lean_object* v_key_60_; lean_object* v_value_61_; lean_object* v_tail_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_93_; 
v_key_60_ = lean_ctor_get(v_x_59_, 0);
v_value_61_ = lean_ctor_get(v_x_59_, 1);
v_tail_62_ = lean_ctor_get(v_x_59_, 2);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_93_ == 0)
{
v___x_64_ = v_x_59_;
v_isShared_65_ = v_isSharedCheck_93_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_tail_62_);
lean_inc(v_value_61_);
lean_inc(v_key_60_);
lean_dec(v_x_59_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_93_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_expr_66_; lean_object* v___x_67_; uint64_t v___y_69_; 
v_expr_66_ = lean_ctor_get(v_key_60_, 1);
v___x_67_ = lean_array_get_size(v_x_58_);
switch(lean_obj_tag(v_expr_66_))
{
case 0:
{
uint64_t v_hashCode_87_; 
v_hashCode_87_ = lean_ctor_get_uint64(v_expr_66_, sizeof(void*)*2);
v___y_69_ = v_hashCode_87_;
goto v___jp_68_;
}
case 1:
{
uint64_t v_hashCode_88_; 
v_hashCode_88_ = lean_ctor_get_uint64(v_expr_66_, sizeof(void*)*2);
v___y_69_ = v_hashCode_88_;
goto v___jp_68_;
}
case 3:
{
uint64_t v_hashCode_89_; 
v_hashCode_89_ = lean_ctor_get_uint64(v_expr_66_, sizeof(void*)*3);
v___y_69_ = v_hashCode_89_;
goto v___jp_68_;
}
case 4:
{
uint64_t v_hashCode_90_; 
v_hashCode_90_ = lean_ctor_get_uint64(v_expr_66_, sizeof(void*)*3);
v___y_69_ = v_hashCode_90_;
goto v___jp_68_;
}
case 5:
{
uint64_t v_hashCode_91_; 
v_hashCode_91_ = lean_ctor_get_uint64(v_expr_66_, sizeof(void*)*5);
v___y_69_ = v_hashCode_91_;
goto v___jp_68_;
}
default: 
{
uint64_t v_hashCode_92_; 
v_hashCode_92_ = lean_ctor_get_uint64(v_expr_66_, sizeof(void*)*4);
v___y_69_ = v_hashCode_92_;
goto v___jp_68_;
}
}
v___jp_68_:
{
uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v_fold_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_70_ = 32ULL;
v___x_71_ = lean_uint64_shift_right(v___y_69_, v___x_70_);
v_fold_72_ = lean_uint64_xor(v___y_69_, v___x_71_);
v___x_73_ = 16ULL;
v___x_74_ = lean_uint64_shift_right(v_fold_72_, v___x_73_);
v___x_75_ = lean_uint64_xor(v_fold_72_, v___x_74_);
v___x_76_ = lean_uint64_to_usize(v___x_75_);
v___x_77_ = lean_usize_of_nat(v___x_67_);
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_sub(v___x_77_, v___x_78_);
v___x_80_ = lean_usize_land(v___x_76_, v___x_79_);
v___x_81_ = lean_array_uget_borrowed(v_x_58_, v___x_80_);
lean_inc(v___x_81_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 2, v___x_81_);
v___x_83_ = v___x_64_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_key_60_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_value_61_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v___x_81_);
v___x_83_ = v_reuseFailAlloc_86_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; 
v___x_84_ = lean_array_uset(v_x_58_, v___x_80_, v___x_83_);
v_x_58_ = v___x_84_;
v_x_59_ = v_tail_62_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(lean_object* v_i_94_, lean_object* v_source_95_, lean_object* v_target_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_array_get_size(v_source_95_);
v___x_98_ = lean_nat_dec_lt(v_i_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec_ref(v_source_95_);
lean_dec(v_i_94_);
return v_target_96_;
}
else
{
lean_object* v_es_99_; lean_object* v___x_100_; lean_object* v_source_101_; lean_object* v_target_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_es_99_ = lean_array_fget(v_source_95_, v_i_94_);
v___x_100_ = lean_box(0);
v_source_101_ = lean_array_fset(v_source_95_, v_i_94_, v___x_100_);
v_target_102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(v_target_96_, v_es_99_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_94_, v___x_103_);
lean_dec(v_i_94_);
v_i_94_ = v___x_104_;
v_source_95_ = v_source_101_;
v_target_96_ = v_target_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(lean_object* v_data_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_nbuckets_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_107_ = lean_array_get_size(v_data_106_);
v___x_108_ = lean_unsigned_to_nat(2u);
v_nbuckets_109_ = lean_nat_mul(v___x_107_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_box(0);
v___x_112_ = lean_mk_array(v_nbuckets_109_, v___x_111_);
v___x_113_ = lean_array_propagate_mark(v_data_106_, v___x_112_);
v___x_114_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(v___x_110_, v_data_106_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(lean_object* v_m_115_, lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
lean_object* v_size_118_; lean_object* v_buckets_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_170_; 
v_size_118_ = lean_ctor_get(v_m_115_, 0);
v_buckets_119_ = lean_ctor_get(v_m_115_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_m_115_);
if (v_isSharedCheck_170_ == 0)
{
v___x_121_ = v_m_115_;
v_isShared_122_ = v_isSharedCheck_170_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_buckets_119_);
lean_inc(v_size_118_);
lean_dec(v_m_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_170_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_expr_123_; lean_object* v___x_124_; uint64_t v___y_126_; 
v_expr_123_ = lean_ctor_get(v_a_116_, 1);
v___x_124_ = lean_array_get_size(v_buckets_119_);
switch(lean_obj_tag(v_expr_123_))
{
case 0:
{
uint64_t v_hashCode_164_; 
v_hashCode_164_ = lean_ctor_get_uint64(v_expr_123_, sizeof(void*)*2);
v___y_126_ = v_hashCode_164_;
goto v___jp_125_;
}
case 1:
{
uint64_t v_hashCode_165_; 
v_hashCode_165_ = lean_ctor_get_uint64(v_expr_123_, sizeof(void*)*2);
v___y_126_ = v_hashCode_165_;
goto v___jp_125_;
}
case 3:
{
uint64_t v_hashCode_166_; 
v_hashCode_166_ = lean_ctor_get_uint64(v_expr_123_, sizeof(void*)*3);
v___y_126_ = v_hashCode_166_;
goto v___jp_125_;
}
case 4:
{
uint64_t v_hashCode_167_; 
v_hashCode_167_ = lean_ctor_get_uint64(v_expr_123_, sizeof(void*)*3);
v___y_126_ = v_hashCode_167_;
goto v___jp_125_;
}
case 5:
{
uint64_t v_hashCode_168_; 
v_hashCode_168_ = lean_ctor_get_uint64(v_expr_123_, sizeof(void*)*5);
v___y_126_ = v_hashCode_168_;
goto v___jp_125_;
}
default: 
{
uint64_t v_hashCode_169_; 
v_hashCode_169_ = lean_ctor_get_uint64(v_expr_123_, sizeof(void*)*4);
v___y_126_ = v_hashCode_169_;
goto v___jp_125_;
}
}
v___jp_125_:
{
uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_bkt_138_; uint8_t v___x_139_; 
v___x_127_ = 32ULL;
v___x_128_ = lean_uint64_shift_right(v___y_126_, v___x_127_);
v_fold_129_ = lean_uint64_xor(v___y_126_, v___x_128_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_124_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v_bkt_138_ = lean_array_uget_borrowed(v_buckets_119_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_116_, v_bkt_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v_size_x27_141_; lean_object* v___x_142_; lean_object* v_buckets_x27_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v_size_x27_141_ = lean_nat_add(v_size_118_, v___x_140_);
lean_dec(v_size_118_);
lean_inc(v_bkt_138_);
v___x_142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_142_, 0, v_a_116_);
lean_ctor_set(v___x_142_, 1, v_b_117_);
lean_ctor_set(v___x_142_, 2, v_bkt_138_);
v_buckets_x27_143_ = lean_array_uset(v_buckets_119_, v___x_137_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_mul(v_size_x27_141_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(3u);
v___x_147_ = lean_nat_div(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_array_get_size(v_buckets_x27_143_);
v___x_149_ = lean_nat_dec_le(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v_val_150_; lean_object* v___x_152_; 
v_val_150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(v_buckets_x27_143_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_val_150_);
lean_ctor_set(v___x_121_, 0, v_size_x27_141_);
v___x_152_ = v___x_121_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_size_x27_141_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_val_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
lean_object* v___x_155_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_buckets_x27_143_);
lean_ctor_set(v___x_121_, 0, v_size_x27_141_);
v___x_155_ = v___x_121_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_x27_141_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_buckets_x27_143_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
lean_object* v___x_157_; lean_object* v_buckets_x27_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc(v_bkt_138_);
v___x_157_ = lean_box(0);
v_buckets_x27_158_ = lean_array_uset(v_buckets_119_, v___x_137_, v___x_157_);
v___x_159_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(v_a_116_, v_b_117_, v_bkt_138_);
v___x_160_ = lean_array_uset(v_buckets_x27_158_, v___x_137_, v___x_159_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_160_);
v___x_162_ = v___x_121_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_118_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v_key_174_; lean_object* v_value_175_; lean_object* v_tail_176_; uint8_t v___x_177_; 
v_key_174_ = lean_ctor_get(v_x_172_, 0);
v_value_175_ = lean_ctor_get(v_x_172_, 1);
v_tail_176_ = lean_ctor_get(v_x_172_, 2);
v___x_177_ = l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey_decEq(v_key_174_, v_a_171_);
if (v___x_177_ == 0)
{
v_x_172_ = v_tail_176_;
goto _start;
}
else
{
lean_object* v___x_179_; 
lean_inc(v_value_175_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_value_175_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg___boxed(lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(v_a_180_, v_x_181_);
lean_dec(v_x_181_);
lean_dec_ref(v_a_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(lean_object* v_m_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_buckets_185_; lean_object* v_expr_186_; lean_object* v___x_187_; uint64_t v___y_189_; 
v_buckets_185_ = lean_ctor_get(v_m_183_, 1);
v_expr_186_ = lean_ctor_get(v_a_184_, 1);
v___x_187_ = lean_array_get_size(v_buckets_185_);
switch(lean_obj_tag(v_expr_186_))
{
case 0:
{
uint64_t v_hashCode_203_; 
v_hashCode_203_ = lean_ctor_get_uint64(v_expr_186_, sizeof(void*)*2);
v___y_189_ = v_hashCode_203_;
goto v___jp_188_;
}
case 1:
{
uint64_t v_hashCode_204_; 
v_hashCode_204_ = lean_ctor_get_uint64(v_expr_186_, sizeof(void*)*2);
v___y_189_ = v_hashCode_204_;
goto v___jp_188_;
}
case 3:
{
uint64_t v_hashCode_205_; 
v_hashCode_205_ = lean_ctor_get_uint64(v_expr_186_, sizeof(void*)*3);
v___y_189_ = v_hashCode_205_;
goto v___jp_188_;
}
case 4:
{
uint64_t v_hashCode_206_; 
v_hashCode_206_ = lean_ctor_get_uint64(v_expr_186_, sizeof(void*)*3);
v___y_189_ = v_hashCode_206_;
goto v___jp_188_;
}
case 5:
{
uint64_t v_hashCode_207_; 
v_hashCode_207_ = lean_ctor_get_uint64(v_expr_186_, sizeof(void*)*5);
v___y_189_ = v_hashCode_207_;
goto v___jp_188_;
}
default: 
{
uint64_t v_hashCode_208_; 
v_hashCode_208_ = lean_ctor_get_uint64(v_expr_186_, sizeof(void*)*4);
v___y_189_ = v_hashCode_208_;
goto v___jp_188_;
}
}
v___jp_188_:
{
uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v_fold_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_190_ = 32ULL;
v___x_191_ = lean_uint64_shift_right(v___y_189_, v___x_190_);
v_fold_192_ = lean_uint64_xor(v___y_189_, v___x_191_);
v___x_193_ = 16ULL;
v___x_194_ = lean_uint64_shift_right(v_fold_192_, v___x_193_);
v___x_195_ = lean_uint64_xor(v_fold_192_, v___x_194_);
v___x_196_ = lean_uint64_to_usize(v___x_195_);
v___x_197_ = lean_usize_of_nat(v___x_187_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_sub(v___x_197_, v___x_198_);
v___x_200_ = lean_usize_land(v___x_196_, v___x_199_);
v___x_201_ = lean_array_uget_borrowed(v_buckets_185_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(v_a_184_, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg___boxed(lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(v_m_209_, v_a_210_);
lean_dec_ref(v_a_210_);
lean_dec_ref(v_m_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(lean_object* v_w_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
switch(lean_obj_tag(v_a_213_))
{
case 0:
{
lean_object* v_idx_217_; lean_object* v___x_218_; lean_object* v_w_219_; lean_object* v_bv_220_; uint8_t v___x_221_; 
v_idx_217_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_idx_217_);
lean_dec_ref_known(v_a_213_, 2);
lean_inc_ref(v_a_214_);
v___x_218_ = lean_apply_1(v_a_214_, v_idx_217_);
v_w_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_w_219_);
v_bv_220_ = lean_ctor_get(v___x_218_, 1);
lean_inc(v_bv_220_);
lean_dec_ref(v___x_218_);
v___x_221_ = lean_nat_dec_eq(v_w_219_, v_w_212_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = l_BitVec_setWidth(v_w_219_, v_w_212_, v_bv_220_);
lean_dec(v_bv_220_);
lean_dec(v_w_212_);
lean_dec(v_w_219_);
return v___x_222_;
}
else
{
lean_dec(v_w_219_);
lean_dec(v_w_212_);
return v_bv_220_;
}
}
case 1:
{
lean_object* v_val_223_; 
lean_dec(v_w_212_);
v_val_223_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_val_223_);
lean_dec_ref_known(v_a_213_, 2);
return v_val_223_;
}
case 2:
{
lean_object* v_w_224_; lean_object* v_start_225_; lean_object* v_expr_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_w_224_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_w_224_);
v_start_225_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_start_225_);
v_expr_226_ = lean_ctor_get(v_a_213_, 3);
lean_inc_ref(v_expr_226_);
lean_dec_ref_known(v_a_213_, 4);
v___x_227_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_224_, v_expr_226_, v_a_214_, v_a_215_);
v___x_228_ = l_BitVec_extractLsb_x27___redArg(v_start_225_, v_w_212_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v_w_212_);
lean_dec(v_start_225_);
return v___x_228_;
}
case 3:
{
lean_object* v_lhs_229_; uint8_t v_op_230_; lean_object* v_rhs_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_lhs_229_ = lean_ctor_get(v_a_213_, 1);
lean_inc_ref(v_lhs_229_);
v_op_230_ = lean_ctor_get_uint8(v_a_213_, sizeof(void*)*3 + 8);
v_rhs_231_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_rhs_231_);
lean_dec_ref_known(v_a_213_, 3);
lean_inc_n(v_w_212_, 2);
v___x_232_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_212_, v_lhs_229_, v_a_214_, v_a_215_);
v___x_233_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_212_, v_rhs_231_, v_a_214_, v_a_215_);
v___x_234_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_212_, v_op_230_, v___x_232_, v___x_233_);
lean_dec(v___x_233_);
lean_dec(v___x_232_);
lean_dec(v_w_212_);
return v___x_234_;
}
case 4:
{
lean_object* v_op_235_; lean_object* v_operand_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_op_235_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_op_235_);
v_operand_236_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_operand_236_);
lean_dec_ref_known(v_a_213_, 3);
lean_inc(v_w_212_);
v___x_237_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_212_, v_operand_236_, v_a_214_, v_a_215_);
v___x_238_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_212_, v_op_235_, v___x_237_);
lean_dec(v_op_235_);
return v___x_238_;
}
case 5:
{
lean_object* v_l_239_; lean_object* v_r_240_; lean_object* v_lhs_241_; lean_object* v_rhs_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_w_212_);
v_l_239_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_l_239_);
v_r_240_ = lean_ctor_get(v_a_213_, 1);
lean_inc_n(v_r_240_, 2);
v_lhs_241_ = lean_ctor_get(v_a_213_, 3);
lean_inc_ref(v_lhs_241_);
v_rhs_242_ = lean_ctor_get(v_a_213_, 4);
lean_inc_ref(v_rhs_242_);
lean_dec_ref_known(v_a_213_, 5);
v___x_243_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_l_239_, v_lhs_241_, v_a_214_, v_a_215_);
v___x_244_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_r_240_, v_rhs_242_, v_a_214_, v_a_215_);
v___x_245_ = l_BitVec_append___redArg(v_r_240_, v___x_243_, v___x_244_);
lean_dec(v___x_244_);
lean_dec(v___x_243_);
lean_dec(v_r_240_);
return v___x_245_;
}
case 6:
{
lean_object* v_w_246_; lean_object* v_n_247_; lean_object* v_expr_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_w_212_);
v_w_246_ = lean_ctor_get(v_a_213_, 0);
lean_inc_n(v_w_246_, 2);
v_n_247_ = lean_ctor_get(v_a_213_, 2);
lean_inc(v_n_247_);
v_expr_248_ = lean_ctor_get(v_a_213_, 3);
lean_inc_ref(v_expr_248_);
lean_dec_ref_known(v_a_213_, 4);
v___x_249_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_246_, v_expr_248_, v_a_214_, v_a_215_);
v___x_250_ = l_BitVec_replicate(v_w_246_, v_n_247_, v___x_249_);
lean_dec(v___x_249_);
lean_dec(v_n_247_);
lean_dec(v_w_246_);
return v___x_250_;
}
case 7:
{
lean_object* v_n_251_; lean_object* v_lhs_252_; lean_object* v_rhs_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_n_251_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_n_251_);
v_lhs_252_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_lhs_252_);
v_rhs_253_ = lean_ctor_get(v_a_213_, 3);
lean_inc_ref(v_rhs_253_);
lean_dec_ref_known(v_a_213_, 4);
lean_inc(v_w_212_);
v___x_254_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_212_, v_lhs_252_, v_a_214_, v_a_215_);
v___x_255_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_n_251_, v_rhs_253_, v_a_214_, v_a_215_);
v___x_256_ = l_BitVec_shiftLeft(v_w_212_, v___x_254_, v___x_255_);
lean_dec(v___x_255_);
lean_dec(v___x_254_);
lean_dec(v_w_212_);
return v___x_256_;
}
case 8:
{
lean_object* v_n_257_; lean_object* v_lhs_258_; lean_object* v_rhs_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_n_257_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_n_257_);
v_lhs_258_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_lhs_258_);
v_rhs_259_ = lean_ctor_get(v_a_213_, 3);
lean_inc_ref(v_rhs_259_);
lean_dec_ref_known(v_a_213_, 4);
v___x_260_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_212_, v_lhs_258_, v_a_214_, v_a_215_);
v___x_261_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_n_257_, v_rhs_259_, v_a_214_, v_a_215_);
v___x_262_ = lean_nat_shiftr(v___x_260_, v___x_261_);
lean_dec(v___x_261_);
lean_dec(v___x_260_);
return v___x_262_;
}
default: 
{
lean_object* v_n_263_; lean_object* v_lhs_264_; lean_object* v_rhs_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_n_263_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_n_263_);
v_lhs_264_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_lhs_264_);
v_rhs_265_ = lean_ctor_get(v_a_213_, 3);
lean_inc_ref(v_rhs_265_);
lean_dec_ref_known(v_a_213_, 4);
lean_inc(v_w_212_);
v___x_266_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_212_, v_lhs_264_, v_a_214_, v_a_215_);
v___x_267_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_n_263_, v_rhs_265_, v_a_214_, v_a_215_);
v___x_268_ = l_BitVec_sshiftRight(v_w_212_, v___x_266_, v___x_267_);
lean_dec(v___x_267_);
lean_dec(v_w_212_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(lean_object* v_w_269_, lean_object* v_expr_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_key_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc_ref(v_expr_270_);
lean_inc(v_w_269_);
v_key_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_274_, 0, v_w_269_);
lean_ctor_set(v_key_274_, 1, v_expr_270_);
v___x_275_ = lean_st_ref_get(v_a_272_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(v___x_275_, v_key_274_);
lean_dec(v___x_275_);
if (lean_obj_tag(v___x_276_) == 1)
{
lean_object* v_val_277_; 
lean_dec_ref_known(v_key_274_, 2);
lean_dec_ref(v_expr_270_);
lean_dec(v_w_269_);
v_val_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v___x_276_, 1);
return v_val_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v___x_276_);
v___x_278_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_269_, v_expr_270_, v_a_271_, v_a_272_);
v___x_279_ = lean_st_ref_take(v_a_272_);
lean_inc(v___x_278_);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(v___x_279_, v_key_274_, v___x_278_);
v___x_281_ = lean_st_ref_put(v_a_272_, v___x_280_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg___boxed(lean_object* v_w_282_, lean_object* v_expr_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_282_, v_expr_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg___boxed(lean_object* v_w_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go(lean_object* v_00_u03c3_294_, lean_object* v_w_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___redArg(v_w_295_, v_a_296_, v_a_297_, v_a_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go___boxed(lean_object* v_00_u03c3_301_, lean_object* v_w_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_go(v_00_u03c3_301_, v_w_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM(lean_object* v_w_308_, lean_object* v_00_u03c3_309_, lean_object* v_expr_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_308_, v_expr_310_, v_a_311_, v_a_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___boxed(lean_object* v_w_315_, lean_object* v_00_u03c3_316_, lean_object* v_expr_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM(v_w_315_, v_00_u03c3_316_, v_expr_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1(lean_object* v_00_u03b2_322_, lean_object* v_inst_323_, lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___redArg(v_m_324_, v_a_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1___boxed(lean_object* v_00_u03b2_327_, lean_object* v_inst_328_, lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1(v_00_u03b2_327_, v_inst_328_, v_m_329_, v_a_330_);
lean_dec_ref(v_a_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2(lean_object* v_00_u03b2_332_, lean_object* v_m_333_, lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2___redArg(v_m_333_, v_a_334_, v_b_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1(lean_object* v_00_u03b2_337_, lean_object* v_inst_338_, lean_object* v_a_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___redArg(v_a_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1___boxed(lean_object* v_00_u03b2_342_, lean_object* v_inst_343_, lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___at___00Std_DHashMap_Internal_Raw_u2080_get_x3f___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__1_spec__1(v_00_u03b2_342_, v_inst_343_, v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3(lean_object* v_00_u03b2_347_, lean_object* v_a_348_, lean_object* v_x_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___redArg(v_a_348_, v_x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3___boxed(lean_object* v_00_u03b2_351_, lean_object* v_a_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__3(v_00_u03b2_351_, v_a_352_, v_x_353_);
lean_dec(v_x_353_);
lean_dec_ref(v_a_352_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4(lean_object* v_00_u03b2_356_, lean_object* v_data_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4___redArg(v_data_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5(lean_object* v_00_u03b2_359_, lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__5___redArg(v_a_360_, v_b_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_364_, lean_object* v_i_365_, lean_object* v_source_366_, lean_object* v_target_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5___redArg(v_i_365_, v_source_366_, v_target_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM_spec__2_spec__4_spec__5_spec__6___redArg(v_x_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(lean_object* v_expr_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
if (lean_obj_tag(v_expr_373_) == 0)
{
lean_object* v_w_377_; lean_object* v_lhs_378_; uint8_t v_op_379_; lean_object* v_rhs_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_w_377_ = lean_ctor_get(v_expr_373_, 0);
lean_inc_n(v_w_377_, 2);
v_lhs_378_ = lean_ctor_get(v_expr_373_, 1);
lean_inc_ref(v_lhs_378_);
v_op_379_ = lean_ctor_get_uint8(v_expr_373_, sizeof(void*)*3);
v_rhs_380_ = lean_ctor_get(v_expr_373_, 2);
lean_inc_ref(v_rhs_380_);
lean_dec_ref_known(v_expr_373_, 3);
v___x_381_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_377_, v_lhs_378_, v_a_374_, v_a_375_);
v___x_382_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_377_, v_rhs_380_, v_a_374_, v_a_375_);
v___x_383_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_379_, v___x_381_, v___x_382_);
lean_dec(v___x_382_);
lean_dec(v___x_381_);
return v___x_383_;
}
else
{
lean_object* v_w_384_; lean_object* v_expr_385_; lean_object* v_idx_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_w_384_ = lean_ctor_get(v_expr_373_, 0);
lean_inc(v_w_384_);
v_expr_385_ = lean_ctor_get(v_expr_373_, 1);
lean_inc_ref(v_expr_385_);
v_idx_386_ = lean_ctor_get(v_expr_373_, 2);
lean_inc(v_idx_386_);
lean_dec_ref_known(v_expr_373_, 3);
v___x_387_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_384_, v_expr_385_, v_a_374_, v_a_375_);
v___x_388_ = l_Nat_testBit(v___x_387_, v_idx_386_);
lean_dec(v_idx_386_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg___boxed(lean_object* v_expr_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM(lean_object* v_00_u03c3_395_, lean_object* v_expr_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_396_, v_a_397_, v_a_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___boxed(lean_object* v_00_u03c3_401_, lean_object* v_expr_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM(v_00_u03c3_401_, v_expr_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(lean_object* v_expr_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
switch(lean_obj_tag(v_expr_408_))
{
case 0:
{
lean_object* v_a_412_; uint8_t v___x_413_; 
v_a_412_ = lean_ctor_get(v_expr_408_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v_expr_408_, 1);
v___x_413_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_a_412_, v_a_409_, v_a_410_);
return v___x_413_;
}
case 1:
{
uint8_t v_a_414_; 
v_a_414_ = lean_ctor_get_uint8(v_expr_408_, 0);
lean_dec_ref_known(v_expr_408_, 0);
return v_a_414_;
}
case 2:
{
lean_object* v_a_415_; uint8_t v___x_416_; 
v_a_415_ = lean_ctor_get(v_expr_408_, 0);
lean_inc_ref(v_a_415_);
lean_dec_ref_known(v_expr_408_, 1);
v___x_416_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_415_, v_a_409_, v_a_410_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 1;
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
case 3:
{
uint8_t v_a_419_; lean_object* v_a_420_; lean_object* v_a_421_; uint8_t v___x_422_; uint8_t v___x_423_; uint8_t v___x_424_; 
v_a_419_ = lean_ctor_get_uint8(v_expr_408_, sizeof(void*)*2);
v_a_420_ = lean_ctor_get(v_expr_408_, 0);
lean_inc_ref(v_a_420_);
v_a_421_ = lean_ctor_get(v_expr_408_, 1);
lean_inc_ref(v_a_421_);
lean_dec_ref_known(v_expr_408_, 2);
v___x_422_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_420_, v_a_409_, v_a_410_);
v___x_423_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_421_, v_a_409_, v_a_410_);
v___x_424_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_419_, v___x_422_, v___x_423_);
return v___x_424_;
}
default: 
{
lean_object* v_a_425_; lean_object* v_a_426_; lean_object* v_a_427_; uint8_t v___x_428_; 
v_a_425_ = lean_ctor_get(v_expr_408_, 0);
lean_inc_ref(v_a_425_);
v_a_426_ = lean_ctor_get(v_expr_408_, 1);
lean_inc_ref(v_a_426_);
v_a_427_ = lean_ctor_get(v_expr_408_, 2);
lean_inc_ref(v_a_427_);
lean_dec_ref_known(v_expr_408_, 3);
v___x_428_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_a_425_, v_a_409_, v_a_410_);
if (v___x_428_ == 0)
{
lean_dec_ref(v_a_426_);
v_expr_408_ = v_a_427_;
goto _start;
}
else
{
lean_dec_ref(v_a_427_);
v_expr_408_ = v_a_426_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg___boxed(lean_object* v_expr_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM(lean_object* v_00_u03c3_437_, lean_object* v_expr_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_438_, v_a_439_, v_a_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___boxed(lean_object* v_00_u03c3_443_, lean_object* v_expr_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM(v_00_u03c3_443_, v_expr_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0(lean_object* v_w_450_, lean_object* v_expr_451_, lean_object* v_assign_452_, lean_object* v_00_u03c3_453_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_456_ = lean_st_mk_ref(v___x_455_);
v___x_457_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficientM___redArg(v_w_450_, v_expr_451_, v_assign_452_, v___x_456_);
v___x_458_ = lean_st_ref_get(v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_458_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0___boxed(lean_object* v_w_459_, lean_object* v_expr_460_, lean_object* v_assign_461_, lean_object* v_00_u03c3_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0(v_w_459_, v_expr_460_, v_assign_461_, v_00_u03c3_462_);
lean_dec_ref(v_assign_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient(lean_object* v_w_465_, lean_object* v_assign_466_, lean_object* v_expr_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; 
v___f_468_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_EfficientEval_BVExpr_evalEfficient___lam__0___boxed), 5, 3);
lean_closure_set(v___f_468_, 0, v_w_465_);
lean_closure_set(v___f_468_, 1, v_expr_467_);
lean_closure_set(v___f_468_, 2, v_assign_466_);
v___x_469_ = l_runST___redArg(v___f_468_);
return v___x_469_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0(lean_object* v_expr_470_, lean_object* v_assign_471_, lean_object* v_00_u03c3_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_475_ = lean_st_mk_ref(v___x_474_);
v___x_476_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficientM___redArg(v_expr_470_, v_assign_471_, v___x_475_);
v___x_477_ = lean_st_ref_get(v___x_475_);
lean_dec(v___x_475_);
lean_dec(v___x_477_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0___boxed(lean_object* v_expr_478_, lean_object* v_assign_479_, lean_object* v_00_u03c3_480_, lean_object* v___y_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0(v_expr_478_, v_assign_479_, v_00_u03c3_480_);
lean_dec_ref(v_assign_479_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient(lean_object* v_assign_484_, lean_object* v_expr_485_){
_start:
{
lean_object* v___f_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___f_486_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___lam__0___boxed), 4, 2);
lean_closure_set(v___f_486_, 0, v_expr_485_);
lean_closure_set(v___f_486_, 1, v_assign_484_);
v___x_487_ = l_runST___redArg(v___f_486_);
v___x_488_ = lean_unbox(v___x_487_);
lean_dec(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient___boxed(lean_object* v_assign_489_, lean_object* v_expr_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Std_Tactic_BVDecide_EfficientEval_BVPred_evalEfficient(v_assign_489_, v_expr_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0(lean_object* v_expr_493_, lean_object* v_assign_494_, lean_object* v_00_u03c3_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_EvalM_run___redArg___lam__0___closed__1);
v___x_498_ = lean_st_mk_ref(v___x_497_);
v___x_499_ = l___private_Std_Tactic_BVDecide_Bitblast_EfficientEval_0__Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficientM___redArg(v_expr_493_, v_assign_494_, v___x_498_);
v___x_500_ = lean_st_ref_get(v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_500_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0___boxed(lean_object* v_expr_501_, lean_object* v_assign_502_, lean_object* v_00_u03c3_503_, lean_object* v___y_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0(v_expr_501_, v_assign_502_, v_00_u03c3_503_);
lean_dec_ref(v_assign_502_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient(lean_object* v_assign_507_, lean_object* v_expr_508_){
_start:
{
lean_object* v___f_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___f_509_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___lam__0___boxed), 4, 2);
lean_closure_set(v___f_509_, 0, v_expr_508_);
lean_closure_set(v___f_509_, 1, v_assign_507_);
v___x_510_ = l_runST___redArg(v___f_509_);
v___x_511_ = lean_unbox(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient___boxed(lean_object* v_assign_512_, lean_object* v_expr_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Std_Tactic_BVDecide_EfficientEval_BVLogicalExpr_evalEfficient(v_assign_512_, v_expr_513_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
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
