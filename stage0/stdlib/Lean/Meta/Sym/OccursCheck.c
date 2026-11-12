// Lean compiler output
// Module: Lean.Meta.Sym.OccursCheck
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_occursCheck___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_occursCheck___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_occursCheck___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_occursCheck___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_occursCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_occursCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg(lean_object* v_mvarId_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_mctx_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_mctx_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_mctx_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_5_, v_mvarId_1_);
lean_dec_ref(v_mctx_5_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg___boxed(lean_object* v_mvarId_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg(v_mvarId_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec(v_mvarId_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0(lean_object* v_mvarId_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg(v_mvarId_12_, v___y_17_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___boxed(lean_object* v_mvarId_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0(v_mvarId_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec(v_mvarId_22_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg(lean_object* v_mvarId_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; lean_object* v_mctx_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_st_ref_get(v___y_33_);
v_mctx_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_mctx_36_);
lean_dec(v___x_35_);
v___x_37_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_36_, v_mvarId_32_);
lean_dec_ref(v_mctx_36_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg___boxed(lean_object* v_mvarId_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg(v_mvarId_39_, v___y_40_);
lean_dec(v___y_40_);
lean_dec(v_mvarId_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1(lean_object* v_mvarId_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg(v_mvarId_43_, v___y_48_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___boxed(lean_object* v_mvarId_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1(v_mvarId_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec(v_mvarId_53_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg(lean_object* v_a_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
else
{
lean_object* v_key_66_; lean_object* v_tail_67_; size_t v___x_68_; size_t v___x_69_; uint8_t v___x_70_; 
v_key_66_ = lean_ctor_get(v_x_64_, 0);
v_tail_67_ = lean_ctor_get(v_x_64_, 2);
v___x_68_ = lean_ptr_addr(v_key_66_);
v___x_69_ = lean_ptr_addr(v_a_63_);
v___x_70_ = lean_usize_dec_eq(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
v_x_64_ = v_tail_67_;
goto _start;
}
else
{
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg___boxed(lean_object* v_a_72_, lean_object* v_x_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg(v_a_72_, v_x_73_);
lean_dec(v_x_73_);
lean_dec_ref(v_a_72_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg(lean_object* v_m_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_buckets_78_; lean_object* v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v_fold_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_buckets_78_ = lean_ctor_get(v_m_76_, 1);
v___x_79_ = lean_array_get_size(v_buckets_78_);
v___x_80_ = lean_ptr_addr(v_a_77_);
v___x_81_ = ((size_t)3ULL);
v___x_82_ = lean_usize_shift_right(v___x_80_, v___x_81_);
v___x_83_ = lean_usize_to_uint64(v___x_82_);
v___x_84_ = 32ULL;
v___x_85_ = lean_uint64_shift_right(v___x_83_, v___x_84_);
v_fold_86_ = lean_uint64_xor(v___x_83_, v___x_85_);
v___x_87_ = 16ULL;
v___x_88_ = lean_uint64_shift_right(v_fold_86_, v___x_87_);
v___x_89_ = lean_uint64_xor(v_fold_86_, v___x_88_);
v___x_90_ = lean_uint64_to_usize(v___x_89_);
v___x_91_ = lean_usize_of_nat(v___x_79_);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_sub(v___x_91_, v___x_92_);
v___x_94_ = lean_usize_land(v___x_90_, v___x_93_);
v___x_95_ = lean_array_uget_borrowed(v_buckets_78_, v___x_94_);
v___x_96_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg(v_a_77_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg___boxed(lean_object* v_m_97_, lean_object* v_a_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg(v_m_97_, v_a_98_);
lean_dec_ref(v_a_98_);
lean_dec_ref(v_m_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
return v_x_101_;
}
else
{
lean_object* v_key_103_; lean_object* v_value_104_; lean_object* v_tail_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_131_; 
v_key_103_ = lean_ctor_get(v_x_102_, 0);
v_value_104_ = lean_ctor_get(v_x_102_, 1);
v_tail_105_ = lean_ctor_get(v_x_102_, 2);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_131_ == 0)
{
v___x_107_ = v_x_102_;
v_isShared_108_ = v_isSharedCheck_131_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_tail_105_);
lean_inc(v_value_104_);
lean_inc(v_key_103_);
lean_dec(v_x_102_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_131_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v_fold_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_109_ = lean_array_get_size(v_x_101_);
v___x_110_ = lean_ptr_addr(v_key_103_);
v___x_111_ = ((size_t)3ULL);
v___x_112_ = lean_usize_shift_right(v___x_110_, v___x_111_);
v___x_113_ = lean_usize_to_uint64(v___x_112_);
v___x_114_ = 32ULL;
v___x_115_ = lean_uint64_shift_right(v___x_113_, v___x_114_);
v_fold_116_ = lean_uint64_xor(v___x_113_, v___x_115_);
v___x_117_ = 16ULL;
v___x_118_ = lean_uint64_shift_right(v_fold_116_, v___x_117_);
v___x_119_ = lean_uint64_xor(v_fold_116_, v___x_118_);
v___x_120_ = lean_uint64_to_usize(v___x_119_);
v___x_121_ = lean_usize_of_nat(v___x_109_);
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_sub(v___x_121_, v___x_122_);
v___x_124_ = lean_usize_land(v___x_120_, v___x_123_);
v___x_125_ = lean_array_uget_borrowed(v_x_101_, v___x_124_);
lean_inc(v___x_125_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 2, v___x_125_);
v___x_127_ = v___x_107_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_key_103_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_value_104_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v___x_125_);
v___x_127_ = v_reuseFailAlloc_130_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; 
v___x_128_ = lean_array_uset(v_x_101_, v___x_124_, v___x_127_);
v_x_101_ = v___x_128_;
v_x_102_ = v_tail_105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5___redArg(lean_object* v_i_132_, lean_object* v_source_133_, lean_object* v_target_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_array_get_size(v_source_133_);
v___x_136_ = lean_nat_dec_lt(v_i_132_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v_source_133_);
lean_dec(v_i_132_);
return v_target_134_;
}
else
{
lean_object* v_es_137_; lean_object* v___x_138_; lean_object* v_source_139_; lean_object* v_target_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_es_137_ = lean_array_fget(v_source_133_, v_i_132_);
v___x_138_ = lean_box(0);
v_source_139_ = lean_array_fset(v_source_133_, v_i_132_, v___x_138_);
v_target_140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5_spec__6___redArg(v_target_134_, v_es_137_);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_add(v_i_132_, v___x_141_);
lean_dec(v_i_132_);
v_i_132_ = v___x_142_;
v_source_133_ = v_source_139_;
v_target_134_ = v_target_140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4___redArg(lean_object* v_data_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_nbuckets_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_145_ = lean_array_get_size(v_data_144_);
v___x_146_ = lean_unsigned_to_nat(2u);
v_nbuckets_147_ = lean_nat_mul(v___x_145_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_box(0);
v___x_150_ = lean_mk_array(v_nbuckets_147_, v___x_149_);
v___x_151_ = lean_array_propagate_mark(v_data_144_, v___x_150_);
v___x_152_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5___redArg(v___x_148_, v_data_144_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3___redArg(lean_object* v_m_153_, lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
lean_object* v_size_156_; lean_object* v_buckets_157_; lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v_fold_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v_bkt_174_; uint8_t v___x_175_; 
v_size_156_ = lean_ctor_get(v_m_153_, 0);
v_buckets_157_ = lean_ctor_get(v_m_153_, 1);
v___x_158_ = lean_array_get_size(v_buckets_157_);
v___x_159_ = lean_ptr_addr(v_a_154_);
v___x_160_ = ((size_t)3ULL);
v___x_161_ = lean_usize_shift_right(v___x_159_, v___x_160_);
v___x_162_ = lean_usize_to_uint64(v___x_161_);
v___x_163_ = 32ULL;
v___x_164_ = lean_uint64_shift_right(v___x_162_, v___x_163_);
v_fold_165_ = lean_uint64_xor(v___x_162_, v___x_164_);
v___x_166_ = 16ULL;
v___x_167_ = lean_uint64_shift_right(v_fold_165_, v___x_166_);
v___x_168_ = lean_uint64_xor(v_fold_165_, v___x_167_);
v___x_169_ = lean_uint64_to_usize(v___x_168_);
v___x_170_ = lean_usize_of_nat(v___x_158_);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_sub(v___x_170_, v___x_171_);
v___x_173_ = lean_usize_land(v___x_169_, v___x_172_);
v_bkt_174_ = lean_array_uget_borrowed(v_buckets_157_, v___x_173_);
v___x_175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg(v_a_154_, v_bkt_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_196_; 
lean_inc_ref(v_buckets_157_);
lean_inc(v_size_156_);
v_isSharedCheck_196_ = !lean_is_exclusive(v_m_153_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; lean_object* v_unused_198_; 
v_unused_197_ = lean_ctor_get(v_m_153_, 1);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_m_153_, 0);
lean_dec(v_unused_198_);
v___x_177_ = v_m_153_;
v_isShared_178_ = v_isSharedCheck_196_;
goto v_resetjp_176_;
}
else
{
lean_dec(v_m_153_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_196_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v_size_x27_180_; lean_object* v___x_181_; lean_object* v_buckets_x27_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v_size_x27_180_ = lean_nat_add(v_size_156_, v___x_179_);
lean_dec(v_size_156_);
lean_inc(v_bkt_174_);
v___x_181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_181_, 0, v_a_154_);
lean_ctor_set(v___x_181_, 1, v_b_155_);
lean_ctor_set(v___x_181_, 2, v_bkt_174_);
v_buckets_x27_182_ = lean_array_uset(v_buckets_157_, v___x_173_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(4u);
v___x_184_ = lean_nat_mul(v_size_x27_180_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(3u);
v___x_186_ = lean_nat_div(v___x_184_, v___x_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_array_get_size(v_buckets_x27_182_);
v___x_188_ = lean_nat_dec_le(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
if (v___x_188_ == 0)
{
lean_object* v_val_189_; lean_object* v___x_191_; 
v_val_189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4___redArg(v_buckets_x27_182_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_val_189_);
lean_ctor_set(v___x_177_, 0, v_size_x27_180_);
v___x_191_ = v___x_177_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_size_x27_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_val_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_194_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_buckets_x27_182_);
lean_ctor_set(v___x_177_, 0, v_size_x27_180_);
v___x_194_ = v___x_177_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_x27_180_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_buckets_x27_182_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_dec(v_b_155_);
lean_dec_ref(v_a_154_);
return v_m_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(lean_object* v_mvarId_199_, lean_object* v_e_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_d_210_; lean_object* v_b_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; uint8_t v___x_223_; 
v___x_223_ = l_Lean_Expr_hasExprMVar(v_e_200_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v_e_200_);
v___x_224_ = lean_box(v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
else
{
if (lean_obj_tag(v_e_200_) == 2)
{
lean_object* v_mvarId_226_; uint8_t v___x_227_; 
v_mvarId_226_ = lean_ctor_get(v_e_200_, 0);
lean_inc(v_mvarId_226_);
lean_dec_ref_known(v_e_200_, 1);
v___x_227_ = l_Lean_instBEqMVarId_beq(v_mvarId_226_, v_mvarId_199_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__0___redArg(v_mvarId_226_, v_a_205_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
if (lean_obj_tag(v_a_229_) == 1)
{
lean_object* v_val_230_; 
lean_dec(v_mvarId_226_);
v_val_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v_a_229_, 1);
v_e_200_ = v_val_230_;
goto _start;
}
else
{
lean_object* v___x_232_; 
lean_dec(v_a_229_);
v___x_232_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__1___redArg(v_mvarId_226_, v_a_205_);
lean_dec(v_mvarId_226_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_245_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_245_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
if (lean_obj_tag(v_a_233_) == 1)
{
lean_object* v_val_237_; lean_object* v_mvarIdPending_238_; lean_object* v___x_239_; 
lean_del_object(v___x_235_);
v_val_237_ = lean_ctor_get(v_a_233_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v_a_233_, 1);
v_mvarIdPending_238_ = lean_ctor_get(v_val_237_, 1);
lean_inc(v_mvarIdPending_238_);
lean_dec(v_val_237_);
v___x_239_ = l_Lean_mkMVar(v_mvarIdPending_238_);
v_e_200_ = v___x_239_;
goto _start;
}
else
{
lean_object* v___x_241_; lean_object* v___x_243_; 
lean_dec(v_a_233_);
v___x_241_ = lean_box(v___x_227_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_241_);
v___x_243_ = v___x_235_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_a_246_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_232_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_232_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_mvarId_226_);
v_a_254_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_228_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_228_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_mvarId_226_);
v___x_262_ = lean_box(v___x_223_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
else
{
uint8_t v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = 0;
v___x_265_ = lean_st_ref_get(v_a_201_);
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg(v___x_265_, v_e_200_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_st_ref_take(v_a_201_);
v___x_268_ = lean_box(0);
lean_inc_ref(v_e_200_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3___redArg(v___x_267_, v_e_200_, v___x_268_);
v___x_270_ = lean_st_ref_put(v_a_201_, v___x_269_);
switch(lean_obj_tag(v_e_200_))
{
case 5:
{
lean_object* v_fn_271_; lean_object* v_arg_272_; lean_object* v___x_273_; 
v_fn_271_ = lean_ctor_get(v_e_200_, 0);
lean_inc_ref(v_fn_271_);
v_arg_272_ = lean_ctor_get(v_e_200_, 1);
lean_inc_ref(v_arg_272_);
lean_dec_ref_known(v_e_200_, 2);
v___x_273_ = l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(v_mvarId_199_, v_fn_271_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; uint8_t v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v___x_275_ = lean_unbox(v_a_274_);
if (v___x_275_ == 0)
{
lean_dec_ref_known(v___x_273_, 1);
v_e_200_ = v_arg_272_;
goto _start;
}
else
{
lean_dec_ref(v_arg_272_);
return v___x_273_;
}
}
else
{
lean_dec_ref(v_arg_272_);
return v___x_273_;
}
}
case 6:
{
lean_object* v_binderType_277_; lean_object* v_body_278_; 
v_binderType_277_ = lean_ctor_get(v_e_200_, 1);
lean_inc_ref(v_binderType_277_);
v_body_278_ = lean_ctor_get(v_e_200_, 2);
lean_inc_ref(v_body_278_);
lean_dec_ref_known(v_e_200_, 3);
v_d_210_ = v_binderType_277_;
v_b_211_ = v_body_278_;
v___y_212_ = v_a_201_;
v___y_213_ = v_a_202_;
v___y_214_ = v_a_203_;
v___y_215_ = v_a_204_;
v___y_216_ = v_a_205_;
v___y_217_ = v_a_206_;
v___y_218_ = v_a_207_;
goto v___jp_209_;
}
case 7:
{
lean_object* v_binderType_279_; lean_object* v_body_280_; 
v_binderType_279_ = lean_ctor_get(v_e_200_, 1);
lean_inc_ref(v_binderType_279_);
v_body_280_ = lean_ctor_get(v_e_200_, 2);
lean_inc_ref(v_body_280_);
lean_dec_ref_known(v_e_200_, 3);
v_d_210_ = v_binderType_279_;
v_b_211_ = v_body_280_;
v___y_212_ = v_a_201_;
v___y_213_ = v_a_202_;
v___y_214_ = v_a_203_;
v___y_215_ = v_a_204_;
v___y_216_ = v_a_205_;
v___y_217_ = v_a_206_;
v___y_218_ = v_a_207_;
goto v___jp_209_;
}
case 8:
{
lean_object* v_type_281_; lean_object* v_value_282_; lean_object* v_body_283_; lean_object* v___x_284_; 
v_type_281_ = lean_ctor_get(v_e_200_, 1);
lean_inc_ref(v_type_281_);
v_value_282_ = lean_ctor_get(v_e_200_, 2);
lean_inc_ref(v_value_282_);
v_body_283_ = lean_ctor_get(v_e_200_, 3);
lean_inc_ref(v_body_283_);
lean_dec_ref_known(v_e_200_, 4);
v___x_284_ = l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(v_mvarId_199_, v_type_281_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; uint8_t v___x_286_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v___x_286_ = lean_unbox(v_a_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref_known(v___x_284_, 1);
v___x_287_ = l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(v_mvarId_199_, v_value_282_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; uint8_t v___x_289_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v___x_289_ = lean_unbox(v_a_288_);
if (v___x_289_ == 0)
{
lean_dec_ref_known(v___x_287_, 1);
v_e_200_ = v_body_283_;
goto _start;
}
else
{
lean_dec_ref(v_body_283_);
return v___x_287_;
}
}
else
{
lean_dec_ref(v_body_283_);
return v___x_287_;
}
}
else
{
lean_dec_ref(v_body_283_);
lean_dec_ref(v_value_282_);
return v___x_284_;
}
}
else
{
lean_dec_ref(v_body_283_);
lean_dec_ref(v_value_282_);
return v___x_284_;
}
}
case 10:
{
lean_object* v_expr_291_; 
v_expr_291_ = lean_ctor_get(v_e_200_, 1);
lean_inc_ref(v_expr_291_);
lean_dec_ref_known(v_e_200_, 2);
v_e_200_ = v_expr_291_;
goto _start;
}
case 11:
{
lean_object* v_struct_293_; 
v_struct_293_ = lean_ctor_get(v_e_200_, 2);
lean_inc_ref(v_struct_293_);
lean_dec_ref_known(v_e_200_, 3);
v_e_200_ = v_struct_293_;
goto _start;
}
default: 
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_e_200_);
v___x_295_ = lean_box(v___x_266_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_e_200_);
v___x_297_ = lean_box(v___x_264_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
}
v___jp_209_:
{
lean_object* v___x_219_; 
v___x_219_ = l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(v_mvarId_199_, v_d_210_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; uint8_t v___x_221_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v___x_221_ = lean_unbox(v_a_220_);
if (v___x_221_ == 0)
{
lean_dec_ref_known(v___x_219_, 1);
v_e_200_ = v_b_211_;
v_a_201_ = v___y_212_;
v_a_202_ = v___y_213_;
v_a_203_ = v___y_214_;
v_a_204_ = v___y_215_;
v_a_205_ = v___y_216_;
v_a_206_ = v___y_217_;
v_a_207_ = v___y_218_;
goto _start;
}
else
{
lean_dec_ref(v_b_211_);
return v___x_219_;
}
}
else
{
lean_dec_ref(v_b_211_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn___boxed(lean_object* v_mvarId_299_, lean_object* v_e_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(v_mvarId_299_, v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_mvarId_299_);
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2(lean_object* v_00_u03b2_310_, lean_object* v_m_311_, lean_object* v_a_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___redArg(v_m_311_, v_a_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2___boxed(lean_object* v_00_u03b2_314_, lean_object* v_m_315_, lean_object* v_a_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2(v_00_u03b2_314_, v_m_315_, v_a_316_);
lean_dec_ref(v_a_316_);
lean_dec_ref(v_m_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3___redArg(v_m_320_, v_a_321_, v_b_322_);
return v___x_323_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2(lean_object* v_00_u03b2_324_, lean_object* v_a_325_, lean_object* v_x_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___redArg(v_a_325_, v_x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2___boxed(lean_object* v_00_u03b2_328_, lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__2_spec__2(v_00_u03b2_328_, v_a_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec_ref(v_a_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4(lean_object* v_00_u03b2_333_, lean_object* v_data_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4___redArg(v_data_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_336_, lean_object* v_i_337_, lean_object* v_source_338_, lean_object* v_target_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5___redArg(v_i_337_, v_source_338_, v_target_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn_spec__3_spec__4_spec__5_spec__6___redArg(v_x_342_, v_x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_occursCheck___closed__0(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_unsigned_to_nat(16u);
v___x_347_ = lean_mk_array(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_occursCheck___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_Lean_Meta_Sym_occursCheck___closed__0, &l_Lean_Meta_Sym_occursCheck___closed__0_once, _init_l_Lean_Meta_Sym_occursCheck___closed__0);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_occursCheck(lean_object* v_mvarId_351_, lean_object* v_e_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = l_Lean_Expr_hasExprMVar(v_e_352_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec_ref(v_e_352_);
v___x_361_ = 1;
v___x_362_ = lean_box(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
else
{
uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_364_ = 0;
v___x_365_ = lean_obj_once(&l_Lean_Meta_Sym_occursCheck___closed__1, &l_Lean_Meta_Sym_occursCheck___closed__1_once, _init_l_Lean_Meta_Sym_occursCheck___closed__1);
v___x_366_ = lean_st_mk_ref(v___x_365_);
v___x_367_ = l___private_Lean_Meta_Sym_OccursCheck_0__Lean_Meta_Sym_occursIn(v_mvarId_351_, v_e_352_, v___x_366_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_382_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_382_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_st_ref_get(v___x_366_);
lean_dec(v___x_366_);
lean_dec(v___x_372_);
v___x_373_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(v___x_360_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_374_);
v___x_376_ = v___x_370_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_box(v___x_364_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_378_);
v___x_380_ = v___x_370_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_dec(v___x_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_occursCheck___boxed(lean_object* v_mvarId_383_, lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_Sym_occursCheck(v_mvarId_383_, v_e_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_mvarId_383_);
return v_res_392_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_OccursCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_OccursCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_OccursCheck(builtin);
}
#ifdef __cplusplus
}
#endif
