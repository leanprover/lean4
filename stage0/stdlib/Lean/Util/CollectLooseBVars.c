// Lean compiler output
// Module: Lean.Util.CollectLooseBVars
// Imports: public import Lean.Expr
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__0;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__1;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__2;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__3;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v_fst_8_; lean_object* v_snd_9_; uint8_t v___x_10_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_fst_6_ = lean_ctor_get(v_key_4_, 0);
v_snd_7_ = lean_ctor_get(v_key_4_, 1);
v_fst_8_ = lean_ctor_get(v_a_1_, 0);
v_snd_9_ = lean_ctor_get(v_a_1_, 1);
v___x_10_ = lean_nat_dec_eq(v_fst_6_, v_fst_8_);
if (v___x_10_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = lean_expr_eqv(v_snd_7_, v_snd_9_);
if (v___x_12_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg___boxed(lean_object* v_a_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_14_, v_x_15_);
lean_dec(v_x_15_);
lean_dec_ref(v_a_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(lean_object* v_m_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_buckets_20_; lean_object* v_fst_21_; lean_object* v_snd_22_; lean_object* v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v_fold_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v_buckets_20_ = lean_ctor_get(v_m_18_, 1);
v_fst_21_ = lean_ctor_get(v_a_19_, 0);
v_snd_22_ = lean_ctor_get(v_a_19_, 1);
v___x_23_ = lean_array_get_size(v_buckets_20_);
v___x_24_ = lean_uint64_of_nat(v_fst_21_);
v___x_25_ = l_Lean_Expr_hash(v_snd_22_);
v___x_26_ = lean_uint64_mix_hash(v___x_24_, v___x_25_);
v___x_27_ = 32ULL;
v___x_28_ = lean_uint64_shift_right(v___x_26_, v___x_27_);
v_fold_29_ = lean_uint64_xor(v___x_26_, v___x_28_);
v___x_30_ = 16ULL;
v___x_31_ = lean_uint64_shift_right(v_fold_29_, v___x_30_);
v___x_32_ = lean_uint64_xor(v_fold_29_, v___x_31_);
v___x_33_ = lean_uint64_to_usize(v___x_32_);
v___x_34_ = lean_usize_of_nat(v___x_23_);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_sub(v___x_34_, v___x_35_);
v___x_37_ = lean_usize_land(v___x_33_, v___x_36_);
v___x_38_ = lean_array_uget_borrowed(v_buckets_20_, v___x_37_);
v___x_39_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_19_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(lean_object* v_m_40_, lean_object* v_a_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_40_, v_a_41_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_m_40_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
return v_x_44_;
}
else
{
lean_object* v_key_46_; lean_object* v_value_47_; lean_object* v_tail_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_75_; 
v_key_46_ = lean_ctor_get(v_x_45_, 0);
v_value_47_ = lean_ctor_get(v_x_45_, 1);
v_tail_48_ = lean_ctor_get(v_x_45_, 2);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_75_ == 0)
{
v___x_50_ = v_x_45_;
v_isShared_51_ = v_isSharedCheck_75_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_tail_48_);
lean_inc(v_value_47_);
lean_inc(v_key_46_);
lean_dec(v_x_45_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_75_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v_fold_60_; uint64_t v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v_fst_52_ = lean_ctor_get(v_key_46_, 0);
v_snd_53_ = lean_ctor_get(v_key_46_, 1);
v___x_54_ = lean_array_get_size(v_x_44_);
v___x_55_ = lean_uint64_of_nat(v_fst_52_);
v___x_56_ = l_Lean_Expr_hash(v_snd_53_);
v___x_57_ = lean_uint64_mix_hash(v___x_55_, v___x_56_);
v___x_58_ = 32ULL;
v___x_59_ = lean_uint64_shift_right(v___x_57_, v___x_58_);
v_fold_60_ = lean_uint64_xor(v___x_57_, v___x_59_);
v___x_61_ = 16ULL;
v___x_62_ = lean_uint64_shift_right(v_fold_60_, v___x_61_);
v___x_63_ = lean_uint64_xor(v_fold_60_, v___x_62_);
v___x_64_ = lean_uint64_to_usize(v___x_63_);
v___x_65_ = lean_usize_of_nat(v___x_54_);
v___x_66_ = ((size_t)1ULL);
v___x_67_ = lean_usize_sub(v___x_65_, v___x_66_);
v___x_68_ = lean_usize_land(v___x_64_, v___x_67_);
v___x_69_ = lean_array_uget_borrowed(v_x_44_, v___x_68_);
lean_inc(v___x_69_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v___x_69_);
v___x_71_ = v___x_50_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_key_46_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_value_47_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v___x_69_);
v___x_71_ = v_reuseFailAlloc_74_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; 
v___x_72_ = lean_array_uset(v_x_44_, v___x_68_, v___x_71_);
v_x_44_ = v___x_72_;
v_x_45_ = v_tail_48_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(lean_object* v_i_76_, lean_object* v_source_77_, lean_object* v_target_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_array_get_size(v_source_77_);
v___x_80_ = lean_nat_dec_lt(v_i_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v_source_77_);
lean_dec(v_i_76_);
return v_target_78_;
}
else
{
lean_object* v_es_81_; lean_object* v___x_82_; lean_object* v_source_83_; lean_object* v_target_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_es_81_ = lean_array_fget(v_source_77_, v_i_76_);
v___x_82_ = lean_box(0);
v_source_83_ = lean_array_fset(v_source_77_, v_i_76_, v___x_82_);
v_target_84_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_target_78_, v_es_81_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_76_, v___x_85_);
lean_dec(v_i_76_);
v_i_76_ = v___x_86_;
v_source_77_ = v_source_83_;
v_target_78_ = v_target_84_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(lean_object* v_data_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_nbuckets_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_89_ = lean_array_get_size(v_data_88_);
v___x_90_ = lean_unsigned_to_nat(2u);
v_nbuckets_91_ = lean_nat_mul(v___x_89_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_mk_array(v_nbuckets_91_, v___x_93_);
v___x_95_ = lean_array_propagate_mark(v_data_88_, v___x_94_);
v___x_96_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v___x_92_, v_data_88_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(lean_object* v_m_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_size_100_; lean_object* v_buckets_101_; lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v_fold_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; lean_object* v_bkt_119_; uint8_t v___x_120_; 
v_size_100_ = lean_ctor_get(v_m_97_, 0);
v_buckets_101_ = lean_ctor_get(v_m_97_, 1);
v_fst_102_ = lean_ctor_get(v_a_98_, 0);
v_snd_103_ = lean_ctor_get(v_a_98_, 1);
v___x_104_ = lean_array_get_size(v_buckets_101_);
v___x_105_ = lean_uint64_of_nat(v_fst_102_);
v___x_106_ = l_Lean_Expr_hash(v_snd_103_);
v___x_107_ = lean_uint64_mix_hash(v___x_105_, v___x_106_);
v___x_108_ = 32ULL;
v___x_109_ = lean_uint64_shift_right(v___x_107_, v___x_108_);
v_fold_110_ = lean_uint64_xor(v___x_107_, v___x_109_);
v___x_111_ = 16ULL;
v___x_112_ = lean_uint64_shift_right(v_fold_110_, v___x_111_);
v___x_113_ = lean_uint64_xor(v_fold_110_, v___x_112_);
v___x_114_ = lean_uint64_to_usize(v___x_113_);
v___x_115_ = lean_usize_of_nat(v___x_104_);
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_sub(v___x_115_, v___x_116_);
v___x_118_ = lean_usize_land(v___x_114_, v___x_117_);
v_bkt_119_ = lean_array_uget_borrowed(v_buckets_101_, v___x_118_);
v___x_120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_98_, v_bkt_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_141_; 
lean_inc_ref(v_buckets_101_);
lean_inc(v_size_100_);
v_isSharedCheck_141_ = !lean_is_exclusive(v_m_97_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; lean_object* v_unused_143_; 
v_unused_142_ = lean_ctor_get(v_m_97_, 1);
lean_dec(v_unused_142_);
v_unused_143_ = lean_ctor_get(v_m_97_, 0);
lean_dec(v_unused_143_);
v___x_122_ = v_m_97_;
v_isShared_123_ = v_isSharedCheck_141_;
goto v_resetjp_121_;
}
else
{
lean_dec(v_m_97_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_141_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v_size_x27_125_; lean_object* v___x_126_; lean_object* v_buckets_x27_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v_size_x27_125_ = lean_nat_add(v_size_100_, v___x_124_);
lean_dec(v_size_100_);
lean_inc(v_bkt_119_);
v___x_126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_126_, 0, v_a_98_);
lean_ctor_set(v___x_126_, 1, v_b_99_);
lean_ctor_set(v___x_126_, 2, v_bkt_119_);
v_buckets_x27_127_ = lean_array_uset(v_buckets_101_, v___x_118_, v___x_126_);
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_mul(v_size_x27_125_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = lean_nat_div(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_array_get_size(v_buckets_x27_127_);
v___x_133_ = lean_nat_dec_le(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
if (v___x_133_ == 0)
{
lean_object* v_val_134_; lean_object* v___x_136_; 
v_val_134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_buckets_x27_127_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_val_134_);
lean_ctor_set(v___x_122_, 0, v_size_x27_125_);
v___x_136_ = v___x_122_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_size_x27_125_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_val_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
else
{
lean_object* v___x_139_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_buckets_x27_127_);
lean_ctor_set(v___x_122_, 0, v_size_x27_125_);
v___x_139_ = v___x_122_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_size_x27_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_buckets_x27_127_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_dec(v_b_99_);
lean_dec_ref(v_a_98_);
return v_m_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
return v_x_144_;
}
else
{
lean_object* v_key_146_; lean_object* v_value_147_; lean_object* v_tail_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_171_; 
v_key_146_ = lean_ctor_get(v_x_145_, 0);
v_value_147_ = lean_ctor_get(v_x_145_, 1);
v_tail_148_ = lean_ctor_get(v_x_145_, 2);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_171_ == 0)
{
v___x_150_ = v_x_145_;
v_isShared_151_ = v_isSharedCheck_171_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_tail_148_);
lean_inc(v_value_147_);
lean_inc(v_key_146_);
lean_dec(v_x_145_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_171_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v_fold_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_152_ = lean_array_get_size(v_x_144_);
v___x_153_ = lean_uint64_of_nat(v_key_146_);
v___x_154_ = 32ULL;
v___x_155_ = lean_uint64_shift_right(v___x_153_, v___x_154_);
v_fold_156_ = lean_uint64_xor(v___x_153_, v___x_155_);
v___x_157_ = 16ULL;
v___x_158_ = lean_uint64_shift_right(v_fold_156_, v___x_157_);
v___x_159_ = lean_uint64_xor(v_fold_156_, v___x_158_);
v___x_160_ = lean_uint64_to_usize(v___x_159_);
v___x_161_ = lean_usize_of_nat(v___x_152_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_sub(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_land(v___x_160_, v___x_163_);
v___x_165_ = lean_array_uget_borrowed(v_x_144_, v___x_164_);
lean_inc(v___x_165_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 2, v___x_165_);
v___x_167_ = v___x_150_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_key_146_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_value_147_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v___x_165_);
v___x_167_ = v_reuseFailAlloc_170_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; 
v___x_168_ = lean_array_uset(v_x_144_, v___x_164_, v___x_167_);
v_x_144_ = v___x_168_;
v_x_145_ = v_tail_148_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(lean_object* v_i_172_, lean_object* v_source_173_, lean_object* v_target_174_){
_start:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_array_get_size(v_source_173_);
v___x_176_ = lean_nat_dec_lt(v_i_172_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec_ref(v_source_173_);
lean_dec(v_i_172_);
return v_target_174_;
}
else
{
lean_object* v_es_177_; lean_object* v___x_178_; lean_object* v_source_179_; lean_object* v_target_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_es_177_ = lean_array_fget(v_source_173_, v_i_172_);
v___x_178_ = lean_box(0);
v_source_179_ = lean_array_fset(v_source_173_, v_i_172_, v___x_178_);
v_target_180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_target_174_, v_es_177_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_172_, v___x_181_);
lean_dec(v_i_172_);
v_i_172_ = v___x_182_;
v_source_173_ = v_source_179_;
v_target_174_ = v_target_180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(lean_object* v_data_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_nbuckets_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_185_ = lean_array_get_size(v_data_184_);
v___x_186_ = lean_unsigned_to_nat(2u);
v_nbuckets_187_ = lean_nat_mul(v___x_185_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_box(0);
v___x_190_ = lean_mk_array(v_nbuckets_187_, v___x_189_);
v___x_191_ = lean_array_propagate_mark(v_data_184_, v___x_190_);
v___x_192_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v___x_188_, v_data_184_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object* v_a_193_, lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
else
{
lean_object* v_key_196_; lean_object* v_tail_197_; uint8_t v___x_198_; 
v_key_196_ = lean_ctor_get(v_x_194_, 0);
v_tail_197_ = lean_ctor_get(v_x_194_, 2);
v___x_198_ = lean_nat_dec_eq(v_key_196_, v_a_193_);
if (v___x_198_ == 0)
{
v_x_194_ = v_tail_197_;
goto _start;
}
else
{
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object* v_a_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_200_, v_x_201_);
lean_dec(v_x_201_);
lean_dec(v_a_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object* v_m_204_, lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
lean_object* v_size_207_; lean_object* v_buckets_208_; lean_object* v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v_fold_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v_bkt_222_; uint8_t v___x_223_; 
v_size_207_ = lean_ctor_get(v_m_204_, 0);
v_buckets_208_ = lean_ctor_get(v_m_204_, 1);
v___x_209_ = lean_array_get_size(v_buckets_208_);
v___x_210_ = lean_uint64_of_nat(v_a_205_);
v___x_211_ = 32ULL;
v___x_212_ = lean_uint64_shift_right(v___x_210_, v___x_211_);
v_fold_213_ = lean_uint64_xor(v___x_210_, v___x_212_);
v___x_214_ = 16ULL;
v___x_215_ = lean_uint64_shift_right(v_fold_213_, v___x_214_);
v___x_216_ = lean_uint64_xor(v_fold_213_, v___x_215_);
v___x_217_ = lean_uint64_to_usize(v___x_216_);
v___x_218_ = lean_usize_of_nat(v___x_209_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_sub(v___x_218_, v___x_219_);
v___x_221_ = lean_usize_land(v___x_217_, v___x_220_);
v_bkt_222_ = lean_array_uget_borrowed(v_buckets_208_, v___x_221_);
v___x_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_205_, v_bkt_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_244_; 
lean_inc_ref(v_buckets_208_);
lean_inc(v_size_207_);
v_isSharedCheck_244_ = !lean_is_exclusive(v_m_204_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_245_ = lean_ctor_get(v_m_204_, 1);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_m_204_, 0);
lean_dec(v_unused_246_);
v___x_225_ = v_m_204_;
v_isShared_226_ = v_isSharedCheck_244_;
goto v_resetjp_224_;
}
else
{
lean_dec(v_m_204_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_244_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v_size_x27_228_; lean_object* v___x_229_; lean_object* v_buckets_x27_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v_size_x27_228_ = lean_nat_add(v_size_207_, v___x_227_);
lean_dec(v_size_207_);
lean_inc(v_bkt_222_);
v___x_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_229_, 0, v_a_205_);
lean_ctor_set(v___x_229_, 1, v_b_206_);
lean_ctor_set(v___x_229_, 2, v_bkt_222_);
v_buckets_x27_230_ = lean_array_uset(v_buckets_208_, v___x_221_, v___x_229_);
v___x_231_ = lean_unsigned_to_nat(4u);
v___x_232_ = lean_nat_mul(v_size_x27_228_, v___x_231_);
v___x_233_ = lean_unsigned_to_nat(3u);
v___x_234_ = lean_nat_div(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_array_get_size(v_buckets_x27_230_);
v___x_236_ = lean_nat_dec_le(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
if (v___x_236_ == 0)
{
lean_object* v_val_237_; lean_object* v___x_239_; 
v_val_237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_buckets_x27_230_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_val_237_);
lean_ctor_set(v___x_225_, 0, v_size_x27_228_);
v___x_239_ = v___x_225_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_size_x27_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_val_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
else
{
lean_object* v___x_242_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_buckets_x27_230_);
lean_ctor_set(v___x_225_, 0, v_size_x27_228_);
v___x_242_ = v___x_225_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_size_x27_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_buckets_x27_230_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_dec(v_b_206_);
lean_dec(v_a_205_);
return v_m_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object* v_e_247_, lean_object* v_offset_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_t_251_; lean_object* v_b_252_; lean_object* v___y_253_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = l_Lean_Expr_looseBVarRange(v_e_247_);
v___x_260_ = lean_nat_dec_lt(v_offset_248_, v___x_259_);
lean_dec(v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_offset_248_);
lean_dec_ref(v_e_247_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_a_249_);
return v___x_262_;
}
else
{
lean_object* v_visited_263_; lean_object* v_bvars_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_visited_263_ = lean_ctor_get(v_a_249_, 0);
v_bvars_264_ = lean_ctor_get(v_a_249_, 1);
lean_inc_ref(v_e_247_);
lean_inc(v_offset_248_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_offset_248_);
lean_ctor_set(v___x_265_, 1, v_e_247_);
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_visited_263_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_304_; 
lean_inc_ref(v_bvars_264_);
lean_inc_ref(v_visited_263_);
v_isSharedCheck_304_ = !lean_is_exclusive(v_a_249_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; lean_object* v_unused_306_; 
v_unused_305_ = lean_ctor_get(v_a_249_, 1);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_a_249_, 0);
lean_dec(v_unused_306_);
v___x_268_ = v_a_249_;
v_isShared_269_ = v_isSharedCheck_304_;
goto v_resetjp_267_;
}
else
{
lean_dec(v_a_249_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_304_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_box(0);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_visited_263_, v___x_265_, v___x_270_);
lean_inc_ref(v_bvars_264_);
lean_inc_ref(v___x_271_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_bvars_264_);
v___x_273_ = v_reuseFailAlloc_303_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
switch(lean_obj_tag(v_e_247_))
{
case 0:
{
lean_object* v_deBruijnIndex_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref(v___x_273_);
v_deBruijnIndex_274_ = lean_ctor_get(v_e_247_, 0);
lean_inc(v_deBruijnIndex_274_);
lean_dec_ref_known(v_e_247_, 1);
v___x_275_ = lean_nat_sub(v_deBruijnIndex_274_, v_offset_248_);
lean_dec(v_offset_248_);
lean_dec(v_deBruijnIndex_274_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_bvars_264_, v___x_275_, v___x_270_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_271_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_270_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
return v___x_278_;
}
case 5:
{
lean_object* v_fn_279_; lean_object* v_arg_280_; lean_object* v___x_281_; lean_object* v_snd_282_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
v_fn_279_ = lean_ctor_get(v_e_247_, 0);
lean_inc_ref(v_fn_279_);
v_arg_280_ = lean_ctor_get(v_e_247_, 1);
lean_inc_ref(v_arg_280_);
lean_dec_ref_known(v_e_247_, 2);
lean_inc(v_offset_248_);
v___x_281_ = l_Lean_Expr_CollectLooseBVars_main(v_fn_279_, v_offset_248_, v___x_273_);
v_snd_282_ = lean_ctor_get(v___x_281_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v___x_281_);
v_e_247_ = v_arg_280_;
v_a_249_ = v_snd_282_;
goto _start;
}
case 6:
{
lean_object* v_binderType_284_; lean_object* v_body_285_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
v_binderType_284_ = lean_ctor_get(v_e_247_, 1);
lean_inc_ref(v_binderType_284_);
v_body_285_ = lean_ctor_get(v_e_247_, 2);
lean_inc_ref(v_body_285_);
lean_dec_ref_known(v_e_247_, 3);
v_t_251_ = v_binderType_284_;
v_b_252_ = v_body_285_;
v___y_253_ = v___x_273_;
goto v___jp_250_;
}
case 7:
{
lean_object* v_binderType_286_; lean_object* v_body_287_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
v_binderType_286_ = lean_ctor_get(v_e_247_, 1);
lean_inc_ref(v_binderType_286_);
v_body_287_ = lean_ctor_get(v_e_247_, 2);
lean_inc_ref(v_body_287_);
lean_dec_ref_known(v_e_247_, 3);
v_t_251_ = v_binderType_286_;
v_b_252_ = v_body_287_;
v___y_253_ = v___x_273_;
goto v___jp_250_;
}
case 8:
{
lean_object* v_type_288_; lean_object* v_value_289_; lean_object* v_body_290_; lean_object* v___x_291_; lean_object* v_snd_292_; lean_object* v___x_293_; lean_object* v_snd_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
v_type_288_ = lean_ctor_get(v_e_247_, 1);
lean_inc_ref(v_type_288_);
v_value_289_ = lean_ctor_get(v_e_247_, 2);
lean_inc_ref(v_value_289_);
v_body_290_ = lean_ctor_get(v_e_247_, 3);
lean_inc_ref(v_body_290_);
lean_dec_ref_known(v_e_247_, 4);
lean_inc_n(v_offset_248_, 2);
v___x_291_ = l_Lean_Expr_CollectLooseBVars_main(v_type_288_, v_offset_248_, v___x_273_);
v_snd_292_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_snd_292_);
lean_dec_ref(v___x_291_);
v___x_293_ = l_Lean_Expr_CollectLooseBVars_main(v_value_289_, v_offset_248_, v_snd_292_);
v_snd_294_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_snd_294_);
lean_dec_ref(v___x_293_);
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_offset_248_, v___x_295_);
lean_dec(v_offset_248_);
v_e_247_ = v_body_290_;
v_offset_248_ = v___x_296_;
v_a_249_ = v_snd_294_;
goto _start;
}
case 10:
{
lean_object* v_expr_298_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
v_expr_298_ = lean_ctor_get(v_e_247_, 1);
lean_inc_ref(v_expr_298_);
lean_dec_ref_known(v_e_247_, 2);
v_e_247_ = v_expr_298_;
v_a_249_ = v___x_273_;
goto _start;
}
case 11:
{
lean_object* v_struct_300_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
v_struct_300_ = lean_ctor_get(v_e_247_, 2);
lean_inc_ref(v_struct_300_);
lean_dec_ref_known(v_e_247_, 3);
v_e_247_ = v_struct_300_;
v_a_249_ = v___x_273_;
goto _start;
}
default: 
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_271_);
lean_dec_ref(v_bvars_264_);
lean_dec(v_offset_248_);
lean_dec_ref(v_e_247_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_270_);
lean_ctor_set(v___x_302_, 1, v___x_273_);
return v___x_302_;
}
}
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref_known(v___x_265_, 2);
lean_dec(v_offset_248_);
lean_dec_ref(v_e_247_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_a_249_);
return v___x_308_;
}
}
v___jp_250_:
{
lean_object* v___x_254_; lean_object* v_snd_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_inc(v_offset_248_);
v___x_254_ = l_Lean_Expr_CollectLooseBVars_main(v_t_251_, v_offset_248_, v___y_253_);
v_snd_255_ = lean_ctor_get(v___x_254_, 1);
lean_inc(v_snd_255_);
lean_dec_ref(v___x_254_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_offset_248_, v___x_256_);
lean_dec(v_offset_248_);
v_e_247_ = v_b_252_;
v_offset_248_ = v___x_257_;
v_a_249_ = v_snd_255_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_a_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_310_, v_a_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object* v_00_u03b2_313_, lean_object* v_m_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(v_00_u03b2_313_, v_m_314_, v_a_315_);
lean_dec_ref(v_a_315_);
lean_dec_ref(v_m_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object* v_00_u03b2_318_, lean_object* v_m_319_, lean_object* v_a_320_, lean_object* v_b_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_319_, v_a_320_, v_b_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object* v_00_u03b2_323_, lean_object* v_m_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_324_, v_a_325_, v_b_326_);
return v___x_327_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object* v_00_u03b2_328_, lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object* v_00_u03b2_332_, lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(v_00_u03b2_332_, v_a_333_, v_x_334_);
lean_dec(v_x_334_);
lean_dec_ref(v_a_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object* v_00_u03b2_337_, lean_object* v_data_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_data_338_);
return v___x_339_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object* v_00_u03b2_340_, lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object* v_00_u03b2_344_, lean_object* v_a_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(v_00_u03b2_344_, v_a_345_, v_x_346_);
lean_dec(v_x_346_);
lean_dec(v_a_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5(lean_object* v_00_u03b2_349_, lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_data_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_352_, lean_object* v_i_353_, lean_object* v_source_354_, lean_object* v_target_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_i_353_, v_source_354_, v_target_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_357_, lean_object* v_i_358_, lean_object* v_source_359_, lean_object* v_target_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v_i_358_, v_source_359_, v_target_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_x_363_, v_x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_x_367_, v_x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__0(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_box(0);
v___x_371_ = lean_unsigned_to_nat(16u);
v___x_372_ = lean_mk_array(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__0, &l_Lean_Expr_collectLooseBVars___closed__0_once, _init_l_Lean_Expr_collectLooseBVars___closed__0);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__2(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_unsigned_to_nat(16u);
v___x_378_ = lean_mk_array(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__3(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__2, &l_Lean_Expr_collectLooseBVars___closed__2_once, _init_l_Lean_Expr_collectLooseBVars___closed__2);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__4(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__3, &l_Lean_Expr_collectLooseBVars___closed__3_once, _init_l_Lean_Expr_collectLooseBVars___closed__3);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object* v_e_384_, lean_object* v_offset_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = l_Lean_Expr_hasLooseBVars(v_e_384_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_offset_385_);
lean_dec_ref(v_e_384_);
v___x_387_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__1, &l_Lean_Expr_collectLooseBVars___closed__1_once, _init_l_Lean_Expr_collectLooseBVars___closed__1);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_snd_390_; lean_object* v_bvars_391_; 
v___x_388_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__4, &l_Lean_Expr_collectLooseBVars___closed__4_once, _init_l_Lean_Expr_collectLooseBVars___closed__4);
v___x_389_ = l_Lean_Expr_CollectLooseBVars_main(v_e_384_, v_offset_385_, v___x_388_);
v_snd_390_ = lean_ctor_get(v___x_389_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v___x_389_);
v_bvars_391_ = lean_ctor_get(v_snd_390_, 1);
lean_inc_ref(v_bvars_391_);
lean_dec(v_snd_390_);
return v_bvars_391_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectLooseBVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectLooseBVars(builtin);
}
#ifdef __cplusplus
}
#endif
