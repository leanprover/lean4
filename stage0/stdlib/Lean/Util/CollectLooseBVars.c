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
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_nbuckets_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_89_ = lean_array_get_size(v_data_88_);
v___x_90_ = lean_unsigned_to_nat(2u);
v_nbuckets_91_ = lean_nat_mul(v___x_89_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_mk_array(v_nbuckets_91_, v___x_93_);
v___x_95_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v___x_92_, v_data_88_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(lean_object* v_m_96_, lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_size_99_; lean_object* v_buckets_100_; lean_object* v_fst_101_; lean_object* v_snd_102_; lean_object* v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v_fold_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v_bkt_118_; uint8_t v___x_119_; 
v_size_99_ = lean_ctor_get(v_m_96_, 0);
v_buckets_100_ = lean_ctor_get(v_m_96_, 1);
v_fst_101_ = lean_ctor_get(v_a_97_, 0);
v_snd_102_ = lean_ctor_get(v_a_97_, 1);
v___x_103_ = lean_array_get_size(v_buckets_100_);
v___x_104_ = lean_uint64_of_nat(v_fst_101_);
v___x_105_ = l_Lean_Expr_hash(v_snd_102_);
v___x_106_ = lean_uint64_mix_hash(v___x_104_, v___x_105_);
v___x_107_ = 32ULL;
v___x_108_ = lean_uint64_shift_right(v___x_106_, v___x_107_);
v_fold_109_ = lean_uint64_xor(v___x_106_, v___x_108_);
v___x_110_ = 16ULL;
v___x_111_ = lean_uint64_shift_right(v_fold_109_, v___x_110_);
v___x_112_ = lean_uint64_xor(v_fold_109_, v___x_111_);
v___x_113_ = lean_uint64_to_usize(v___x_112_);
v___x_114_ = lean_usize_of_nat(v___x_103_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_sub(v___x_114_, v___x_115_);
v___x_117_ = lean_usize_land(v___x_113_, v___x_116_);
v_bkt_118_ = lean_array_uget_borrowed(v_buckets_100_, v___x_117_);
v___x_119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_97_, v_bkt_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_140_; 
lean_inc_ref(v_buckets_100_);
lean_inc(v_size_99_);
v_isSharedCheck_140_ = !lean_is_exclusive(v_m_96_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; lean_object* v_unused_142_; 
v_unused_141_ = lean_ctor_get(v_m_96_, 1);
lean_dec(v_unused_141_);
v_unused_142_ = lean_ctor_get(v_m_96_, 0);
lean_dec(v_unused_142_);
v___x_121_ = v_m_96_;
v_isShared_122_ = v_isSharedCheck_140_;
goto v_resetjp_120_;
}
else
{
lean_dec(v_m_96_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_140_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v_size_x27_124_; lean_object* v___x_125_; lean_object* v_buckets_x27_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v_size_x27_124_ = lean_nat_add(v_size_99_, v___x_123_);
lean_dec(v_size_99_);
lean_inc(v_bkt_118_);
v___x_125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_125_, 0, v_a_97_);
lean_ctor_set(v___x_125_, 1, v_b_98_);
lean_ctor_set(v___x_125_, 2, v_bkt_118_);
v_buckets_x27_126_ = lean_array_uset(v_buckets_100_, v___x_117_, v___x_125_);
v___x_127_ = lean_unsigned_to_nat(4u);
v___x_128_ = lean_nat_mul(v_size_x27_124_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(3u);
v___x_130_ = lean_nat_div(v___x_128_, v___x_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_array_get_size(v_buckets_x27_126_);
v___x_132_ = lean_nat_dec_le(v___x_130_, v___x_131_);
lean_dec(v___x_130_);
if (v___x_132_ == 0)
{
lean_object* v_val_133_; lean_object* v___x_135_; 
v_val_133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_buckets_x27_126_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_val_133_);
lean_ctor_set(v___x_121_, 0, v_size_x27_124_);
v___x_135_ = v___x_121_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_x27_124_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_val_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
else
{
lean_object* v___x_138_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_buckets_x27_126_);
lean_ctor_set(v___x_121_, 0, v_size_x27_124_);
v___x_138_ = v___x_121_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_size_x27_124_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_buckets_x27_126_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_dec(v_b_98_);
lean_dec_ref(v_a_97_);
return v_m_96_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
return v_x_143_;
}
else
{
lean_object* v_key_145_; lean_object* v_value_146_; lean_object* v_tail_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_170_; 
v_key_145_ = lean_ctor_get(v_x_144_, 0);
v_value_146_ = lean_ctor_get(v_x_144_, 1);
v_tail_147_ = lean_ctor_get(v_x_144_, 2);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_170_ == 0)
{
v___x_149_ = v_x_144_;
v_isShared_150_ = v_isSharedCheck_170_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_tail_147_);
lean_inc(v_value_146_);
lean_inc(v_key_145_);
lean_dec(v_x_144_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_170_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v_fold_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_151_ = lean_array_get_size(v_x_143_);
v___x_152_ = lean_uint64_of_nat(v_key_145_);
v___x_153_ = 32ULL;
v___x_154_ = lean_uint64_shift_right(v___x_152_, v___x_153_);
v_fold_155_ = lean_uint64_xor(v___x_152_, v___x_154_);
v___x_156_ = 16ULL;
v___x_157_ = lean_uint64_shift_right(v_fold_155_, v___x_156_);
v___x_158_ = lean_uint64_xor(v_fold_155_, v___x_157_);
v___x_159_ = lean_uint64_to_usize(v___x_158_);
v___x_160_ = lean_usize_of_nat(v___x_151_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_sub(v___x_160_, v___x_161_);
v___x_163_ = lean_usize_land(v___x_159_, v___x_162_);
v___x_164_ = lean_array_uget_borrowed(v_x_143_, v___x_163_);
lean_inc(v___x_164_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 2, v___x_164_);
v___x_166_ = v___x_149_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_key_145_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_value_146_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v___x_164_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_array_uset(v_x_143_, v___x_163_, v___x_166_);
v_x_143_ = v___x_167_;
v_x_144_ = v_tail_147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(lean_object* v_i_171_, lean_object* v_source_172_, lean_object* v_target_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_array_get_size(v_source_172_);
v___x_175_ = lean_nat_dec_lt(v_i_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_dec_ref(v_source_172_);
lean_dec(v_i_171_);
return v_target_173_;
}
else
{
lean_object* v_es_176_; lean_object* v___x_177_; lean_object* v_source_178_; lean_object* v_target_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_es_176_ = lean_array_fget(v_source_172_, v_i_171_);
v___x_177_ = lean_box(0);
v_source_178_ = lean_array_fset(v_source_172_, v_i_171_, v___x_177_);
v_target_179_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_target_173_, v_es_176_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_171_, v___x_180_);
lean_dec(v_i_171_);
v_i_171_ = v___x_181_;
v_source_172_ = v_source_178_;
v_target_173_ = v_target_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(lean_object* v_data_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_nbuckets_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_184_ = lean_array_get_size(v_data_183_);
v___x_185_ = lean_unsigned_to_nat(2u);
v_nbuckets_186_ = lean_nat_mul(v___x_184_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_box(0);
v___x_189_ = lean_mk_array(v_nbuckets_186_, v___x_188_);
v___x_190_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v___x_187_, v_data_183_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object* v_a_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
else
{
lean_object* v_key_194_; lean_object* v_tail_195_; uint8_t v___x_196_; 
v_key_194_ = lean_ctor_get(v_x_192_, 0);
v_tail_195_ = lean_ctor_get(v_x_192_, 2);
v___x_196_ = lean_nat_dec_eq(v_key_194_, v_a_191_);
if (v___x_196_ == 0)
{
v_x_192_ = v_tail_195_;
goto _start;
}
else
{
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_198_, v_x_199_);
lean_dec(v_x_199_);
lean_dec(v_a_198_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object* v_m_202_, lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
lean_object* v_size_205_; lean_object* v_buckets_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v_bkt_220_; uint8_t v___x_221_; 
v_size_205_ = lean_ctor_get(v_m_202_, 0);
v_buckets_206_ = lean_ctor_get(v_m_202_, 1);
v___x_207_ = lean_array_get_size(v_buckets_206_);
v___x_208_ = lean_uint64_of_nat(v_a_203_);
v___x_209_ = 32ULL;
v___x_210_ = lean_uint64_shift_right(v___x_208_, v___x_209_);
v_fold_211_ = lean_uint64_xor(v___x_208_, v___x_210_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_207_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v_bkt_220_ = lean_array_uget_borrowed(v_buckets_206_, v___x_219_);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_203_, v_bkt_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_242_; 
lean_inc_ref(v_buckets_206_);
lean_inc(v_size_205_);
v_isSharedCheck_242_ = !lean_is_exclusive(v_m_202_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_243_ = lean_ctor_get(v_m_202_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_m_202_, 0);
lean_dec(v_unused_244_);
v___x_223_ = v_m_202_;
v_isShared_224_ = v_isSharedCheck_242_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_m_202_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_242_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v_size_x27_226_; lean_object* v___x_227_; lean_object* v_buckets_x27_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v_size_x27_226_ = lean_nat_add(v_size_205_, v___x_225_);
lean_dec(v_size_205_);
lean_inc(v_bkt_220_);
v___x_227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_227_, 0, v_a_203_);
lean_ctor_set(v___x_227_, 1, v_b_204_);
lean_ctor_set(v___x_227_, 2, v_bkt_220_);
v_buckets_x27_228_ = lean_array_uset(v_buckets_206_, v___x_219_, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(4u);
v___x_230_ = lean_nat_mul(v_size_x27_226_, v___x_229_);
v___x_231_ = lean_unsigned_to_nat(3u);
v___x_232_ = lean_nat_div(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_array_get_size(v_buckets_x27_228_);
v___x_234_ = lean_nat_dec_le(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
if (v___x_234_ == 0)
{
lean_object* v_val_235_; lean_object* v___x_237_; 
v_val_235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_buckets_x27_228_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_val_235_);
lean_ctor_set(v___x_223_, 0, v_size_x27_226_);
v___x_237_ = v___x_223_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_size_x27_226_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_val_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_object* v___x_240_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_buckets_x27_228_);
lean_ctor_set(v___x_223_, 0, v_size_x27_226_);
v___x_240_ = v___x_223_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_size_x27_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_buckets_x27_228_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_dec(v_b_204_);
lean_dec(v_a_203_);
return v_m_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object* v_e_245_, lean_object* v_offset_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_t_249_; lean_object* v_b_250_; lean_object* v___y_251_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = l_Lean_Expr_looseBVarRange(v_e_245_);
v___x_258_ = lean_nat_dec_lt(v_offset_246_, v___x_257_);
lean_dec(v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_offset_246_);
lean_dec_ref(v_e_245_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_a_247_);
return v___x_260_;
}
else
{
lean_object* v_visited_261_; lean_object* v_bvars_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_visited_261_ = lean_ctor_get(v_a_247_, 0);
v_bvars_262_ = lean_ctor_get(v_a_247_, 1);
lean_inc_ref(v_e_245_);
lean_inc(v_offset_246_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_offset_246_);
lean_ctor_set(v___x_263_, 1, v_e_245_);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_visited_261_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_302_; 
lean_inc_ref(v_bvars_262_);
lean_inc_ref(v_visited_261_);
v_isSharedCheck_302_ = !lean_is_exclusive(v_a_247_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_303_ = lean_ctor_get(v_a_247_, 1);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_a_247_, 0);
lean_dec(v_unused_304_);
v___x_266_ = v_a_247_;
v_isShared_267_ = v_isSharedCheck_302_;
goto v_resetjp_265_;
}
else
{
lean_dec(v_a_247_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_302_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_box(0);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_visited_261_, v___x_263_, v___x_268_);
lean_inc_ref(v_bvars_262_);
lean_inc_ref(v___x_269_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_bvars_262_);
v___x_271_ = v_reuseFailAlloc_301_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
switch(lean_obj_tag(v_e_245_))
{
case 0:
{
lean_object* v_deBruijnIndex_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref(v___x_271_);
v_deBruijnIndex_272_ = lean_ctor_get(v_e_245_, 0);
lean_inc(v_deBruijnIndex_272_);
lean_dec_ref_known(v_e_245_, 1);
v___x_273_ = lean_nat_sub(v_deBruijnIndex_272_, v_offset_246_);
lean_dec(v_offset_246_);
lean_dec(v_deBruijnIndex_272_);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_bvars_262_, v___x_273_, v___x_268_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_269_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_268_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
case 5:
{
lean_object* v_fn_277_; lean_object* v_arg_278_; lean_object* v___x_279_; lean_object* v_snd_280_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
v_fn_277_ = lean_ctor_get(v_e_245_, 0);
lean_inc_ref(v_fn_277_);
v_arg_278_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_arg_278_);
lean_dec_ref_known(v_e_245_, 2);
lean_inc(v_offset_246_);
v___x_279_ = l_Lean_Expr_CollectLooseBVars_main(v_fn_277_, v_offset_246_, v___x_271_);
v_snd_280_ = lean_ctor_get(v___x_279_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v___x_279_);
v_e_245_ = v_arg_278_;
v_a_247_ = v_snd_280_;
goto _start;
}
case 6:
{
lean_object* v_binderType_282_; lean_object* v_body_283_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
v_binderType_282_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_binderType_282_);
v_body_283_ = lean_ctor_get(v_e_245_, 2);
lean_inc_ref(v_body_283_);
lean_dec_ref_known(v_e_245_, 3);
v_t_249_ = v_binderType_282_;
v_b_250_ = v_body_283_;
v___y_251_ = v___x_271_;
goto v___jp_248_;
}
case 7:
{
lean_object* v_binderType_284_; lean_object* v_body_285_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
v_binderType_284_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_binderType_284_);
v_body_285_ = lean_ctor_get(v_e_245_, 2);
lean_inc_ref(v_body_285_);
lean_dec_ref_known(v_e_245_, 3);
v_t_249_ = v_binderType_284_;
v_b_250_ = v_body_285_;
v___y_251_ = v___x_271_;
goto v___jp_248_;
}
case 8:
{
lean_object* v_type_286_; lean_object* v_value_287_; lean_object* v_body_288_; lean_object* v___x_289_; lean_object* v_snd_290_; lean_object* v___x_291_; lean_object* v_snd_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
v_type_286_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_type_286_);
v_value_287_ = lean_ctor_get(v_e_245_, 2);
lean_inc_ref(v_value_287_);
v_body_288_ = lean_ctor_get(v_e_245_, 3);
lean_inc_ref(v_body_288_);
lean_dec_ref_known(v_e_245_, 4);
lean_inc_n(v_offset_246_, 2);
v___x_289_ = l_Lean_Expr_CollectLooseBVars_main(v_type_286_, v_offset_246_, v___x_271_);
v_snd_290_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v___x_289_);
v___x_291_ = l_Lean_Expr_CollectLooseBVars_main(v_value_287_, v_offset_246_, v_snd_290_);
v_snd_292_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_snd_292_);
lean_dec_ref(v___x_291_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_offset_246_, v___x_293_);
lean_dec(v_offset_246_);
v_e_245_ = v_body_288_;
v_offset_246_ = v___x_294_;
v_a_247_ = v_snd_292_;
goto _start;
}
case 10:
{
lean_object* v_expr_296_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
v_expr_296_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_expr_296_);
lean_dec_ref_known(v_e_245_, 2);
v_e_245_ = v_expr_296_;
v_a_247_ = v___x_271_;
goto _start;
}
case 11:
{
lean_object* v_struct_298_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
v_struct_298_ = lean_ctor_get(v_e_245_, 2);
lean_inc_ref(v_struct_298_);
lean_dec_ref_known(v_e_245_, 3);
v_e_245_ = v_struct_298_;
v_a_247_ = v___x_271_;
goto _start;
}
default: 
{
lean_object* v___x_300_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_bvars_262_);
lean_dec(v_offset_246_);
lean_dec_ref(v_e_245_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_268_);
lean_ctor_set(v___x_300_, 1, v___x_271_);
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref_known(v___x_263_, 2);
lean_dec(v_offset_246_);
lean_dec_ref(v_e_245_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_a_247_);
return v___x_306_;
}
}
v___jp_248_:
{
lean_object* v___x_252_; lean_object* v_snd_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_inc(v_offset_246_);
v___x_252_ = l_Lean_Expr_CollectLooseBVars_main(v_t_249_, v_offset_246_, v___y_251_);
v_snd_253_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_snd_253_);
lean_dec_ref(v___x_252_);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_add(v_offset_246_, v___x_254_);
lean_dec(v_offset_246_);
v_e_245_ = v_b_250_;
v_offset_246_ = v___x_255_;
v_a_247_ = v_snd_253_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object* v_00_u03b2_307_, lean_object* v_m_308_, lean_object* v_a_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_308_, v_a_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object* v_00_u03b2_311_, lean_object* v_m_312_, lean_object* v_a_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(v_00_u03b2_311_, v_m_312_, v_a_313_);
lean_dec_ref(v_a_313_);
lean_dec_ref(v_m_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object* v_00_u03b2_316_, lean_object* v_m_317_, lean_object* v_a_318_, lean_object* v_b_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_317_, v_a_318_, v_b_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object* v_00_u03b2_321_, lean_object* v_m_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_322_, v_a_323_, v_b_324_);
return v___x_325_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object* v_00_u03b2_326_, lean_object* v_a_327_, lean_object* v_x_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_327_, v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object* v_00_u03b2_330_, lean_object* v_a_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(v_00_u03b2_330_, v_a_331_, v_x_332_);
lean_dec(v_x_332_);
lean_dec_ref(v_a_331_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object* v_00_u03b2_335_, lean_object* v_data_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_data_336_);
return v___x_337_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object* v_00_u03b2_338_, lean_object* v_a_339_, lean_object* v_x_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object* v_00_u03b2_342_, lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(v_00_u03b2_342_, v_a_343_, v_x_344_);
lean_dec(v_x_344_);
lean_dec(v_a_343_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5(lean_object* v_00_u03b2_347_, lean_object* v_data_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_data_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_350_, lean_object* v_i_351_, lean_object* v_source_352_, lean_object* v_target_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_i_351_, v_source_352_, v_target_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_355_, lean_object* v_i_356_, lean_object* v_source_357_, lean_object* v_target_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v_i_356_, v_source_357_, v_target_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_x_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_x_365_, v_x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__0(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_box(0);
v___x_369_ = lean_unsigned_to_nat(16u);
v___x_370_ = lean_mk_array(v___x_369_, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__0, &l_Lean_Expr_collectLooseBVars___closed__0_once, _init_l_Lean_Expr_collectLooseBVars___closed__0);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__2(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_box(0);
v___x_375_ = lean_unsigned_to_nat(16u);
v___x_376_ = lean_mk_array(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__2, &l_Lean_Expr_collectLooseBVars___closed__2_once, _init_l_Lean_Expr_collectLooseBVars___closed__2);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__4(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__3, &l_Lean_Expr_collectLooseBVars___closed__3_once, _init_l_Lean_Expr_collectLooseBVars___closed__3);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object* v_e_382_, lean_object* v_offset_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = l_Lean_Expr_hasLooseBVars(v_e_382_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec(v_offset_383_);
lean_dec_ref(v_e_382_);
v___x_385_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__1, &l_Lean_Expr_collectLooseBVars___closed__1_once, _init_l_Lean_Expr_collectLooseBVars___closed__1);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_snd_388_; lean_object* v_bvars_389_; 
v___x_386_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__4, &l_Lean_Expr_collectLooseBVars___closed__4_once, _init_l_Lean_Expr_collectLooseBVars___closed__4);
v___x_387_ = l_Lean_Expr_CollectLooseBVars_main(v_e_382_, v_offset_383_, v___x_386_);
v_snd_388_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_snd_388_);
lean_dec_ref(v___x_387_);
v_bvars_389_ = lean_ctor_get(v_snd_388_, 1);
lean_inc_ref(v_bvars_389_);
lean_dec(v_snd_388_);
return v_bvars_389_;
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
