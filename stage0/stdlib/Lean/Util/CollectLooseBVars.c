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
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___y_7_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v_fst_11_; lean_object* v_snd_12_; uint8_t v___x_13_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_fst_9_ = lean_ctor_get(v_key_4_, 0);
v_snd_10_ = lean_ctor_get(v_key_4_, 1);
v_fst_11_ = lean_ctor_get(v_a_1_, 0);
v_snd_12_ = lean_ctor_get(v_a_1_, 1);
v___x_13_ = lean_nat_dec_eq(v_fst_9_, v_fst_11_);
if (v___x_13_ == 0)
{
v___y_7_ = v___x_13_;
goto v___jp_6_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = lean_expr_eqv(v_snd_10_, v_snd_12_);
v___y_7_ = v___x_14_;
goto v___jp_6_;
}
v___jp_6_:
{
if (v___y_7_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___y_7_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg___boxed(lean_object* v_a_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec_ref(v_a_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(lean_object* v_m_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_buckets_21_; lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v_fold_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_buckets_21_ = lean_ctor_get(v_m_19_, 1);
v_fst_22_ = lean_ctor_get(v_a_20_, 0);
v_snd_23_ = lean_ctor_get(v_a_20_, 1);
v___x_24_ = lean_array_get_size(v_buckets_21_);
v___x_25_ = lean_uint64_of_nat(v_fst_22_);
v___x_26_ = l_Lean_Expr_hash(v_snd_23_);
v___x_27_ = lean_uint64_mix_hash(v___x_25_, v___x_26_);
v___x_28_ = 32ULL;
v___x_29_ = lean_uint64_shift_right(v___x_27_, v___x_28_);
v_fold_30_ = lean_uint64_xor(v___x_27_, v___x_29_);
v___x_31_ = 16ULL;
v___x_32_ = lean_uint64_shift_right(v_fold_30_, v___x_31_);
v___x_33_ = lean_uint64_xor(v_fold_30_, v___x_32_);
v___x_34_ = lean_uint64_to_usize(v___x_33_);
v___x_35_ = lean_usize_of_nat(v___x_24_);
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_sub(v___x_35_, v___x_36_);
v___x_38_ = lean_usize_land(v___x_34_, v___x_37_);
v___x_39_ = lean_array_uget_borrowed(v_buckets_21_, v___x_38_);
v___x_40_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_20_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(lean_object* v_m_41_, lean_object* v_a_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_41_, v_a_42_);
lean_dec_ref(v_a_42_);
lean_dec_ref(v_m_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
return v_x_45_;
}
else
{
lean_object* v_key_47_; lean_object* v_value_48_; lean_object* v_tail_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_76_; 
v_key_47_ = lean_ctor_get(v_x_46_, 0);
v_value_48_ = lean_ctor_get(v_x_46_, 1);
v_tail_49_ = lean_ctor_get(v_x_46_, 2);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_46_);
if (v_isSharedCheck_76_ == 0)
{
v___x_51_ = v_x_46_;
v_isShared_52_ = v_isSharedCheck_76_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_tail_49_);
lean_inc(v_value_48_);
lean_inc(v_key_47_);
lean_dec(v_x_46_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_76_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_fst_53_; lean_object* v_snd_54_; lean_object* v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; uint64_t v_fold_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; size_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v_fst_53_ = lean_ctor_get(v_key_47_, 0);
v_snd_54_ = lean_ctor_get(v_key_47_, 1);
v___x_55_ = lean_array_get_size(v_x_45_);
v___x_56_ = lean_uint64_of_nat(v_fst_53_);
v___x_57_ = l_Lean_Expr_hash(v_snd_54_);
v___x_58_ = lean_uint64_mix_hash(v___x_56_, v___x_57_);
v___x_59_ = 32ULL;
v___x_60_ = lean_uint64_shift_right(v___x_58_, v___x_59_);
v_fold_61_ = lean_uint64_xor(v___x_58_, v___x_60_);
v___x_62_ = 16ULL;
v___x_63_ = lean_uint64_shift_right(v_fold_61_, v___x_62_);
v___x_64_ = lean_uint64_xor(v_fold_61_, v___x_63_);
v___x_65_ = lean_uint64_to_usize(v___x_64_);
v___x_66_ = lean_usize_of_nat(v___x_55_);
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_sub(v___x_66_, v___x_67_);
v___x_69_ = lean_usize_land(v___x_65_, v___x_68_);
v___x_70_ = lean_array_uget_borrowed(v_x_45_, v___x_69_);
lean_inc(v___x_70_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 2, v___x_70_);
v___x_72_ = v___x_51_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_key_47_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_value_48_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v___x_70_);
v___x_72_ = v_reuseFailAlloc_75_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = lean_array_uset(v_x_45_, v___x_69_, v___x_72_);
v_x_45_ = v___x_73_;
v_x_46_ = v_tail_49_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(lean_object* v_i_77_, lean_object* v_source_78_, lean_object* v_target_79_){
_start:
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_array_get_size(v_source_78_);
v___x_81_ = lean_nat_dec_lt(v_i_77_, v___x_80_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_source_78_);
lean_dec(v_i_77_);
return v_target_79_;
}
else
{
lean_object* v_es_82_; lean_object* v___x_83_; lean_object* v_source_84_; lean_object* v_target_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_es_82_ = lean_array_fget(v_source_78_, v_i_77_);
v___x_83_ = lean_box(0);
v_source_84_ = lean_array_fset(v_source_78_, v_i_77_, v___x_83_);
v_target_85_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_target_79_, v_es_82_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_i_77_, v___x_86_);
lean_dec(v_i_77_);
v_i_77_ = v___x_87_;
v_source_78_ = v_source_84_;
v_target_79_ = v_target_85_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(lean_object* v_data_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_nbuckets_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_90_ = lean_array_get_size(v_data_89_);
v___x_91_ = lean_unsigned_to_nat(2u);
v_nbuckets_92_ = lean_nat_mul(v___x_90_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_box(0);
v___x_95_ = lean_mk_array(v_nbuckets_92_, v___x_94_);
v___x_96_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v___x_93_, v_data_89_, v___x_95_);
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
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_nbuckets_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_185_ = lean_array_get_size(v_data_184_);
v___x_186_ = lean_unsigned_to_nat(2u);
v_nbuckets_187_ = lean_nat_mul(v___x_185_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_box(0);
v___x_190_ = lean_mk_array(v_nbuckets_187_, v___x_189_);
v___x_191_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v___x_188_, v_data_184_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
else
{
lean_object* v_key_195_; lean_object* v_tail_196_; uint8_t v___x_197_; 
v_key_195_ = lean_ctor_get(v_x_193_, 0);
v_tail_196_ = lean_ctor_get(v_x_193_, 2);
v___x_197_ = lean_nat_dec_eq(v_key_195_, v_a_192_);
if (v___x_197_ == 0)
{
v_x_193_ = v_tail_196_;
goto _start;
}
else
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec(v_a_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object* v_m_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v_size_206_; lean_object* v_buckets_207_; lean_object* v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v_fold_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v_bkt_221_; uint8_t v___x_222_; 
v_size_206_ = lean_ctor_get(v_m_203_, 0);
v_buckets_207_ = lean_ctor_get(v_m_203_, 1);
v___x_208_ = lean_array_get_size(v_buckets_207_);
v___x_209_ = lean_uint64_of_nat(v_a_204_);
v___x_210_ = 32ULL;
v___x_211_ = lean_uint64_shift_right(v___x_209_, v___x_210_);
v_fold_212_ = lean_uint64_xor(v___x_209_, v___x_211_);
v___x_213_ = 16ULL;
v___x_214_ = lean_uint64_shift_right(v_fold_212_, v___x_213_);
v___x_215_ = lean_uint64_xor(v_fold_212_, v___x_214_);
v___x_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = lean_usize_of_nat(v___x_208_);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v___x_217_, v___x_218_);
v___x_220_ = lean_usize_land(v___x_216_, v___x_219_);
v_bkt_221_ = lean_array_uget_borrowed(v_buckets_207_, v___x_220_);
v___x_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_204_, v_bkt_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_243_; 
lean_inc_ref(v_buckets_207_);
lean_inc(v_size_206_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_m_203_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; 
v_unused_244_ = lean_ctor_get(v_m_203_, 1);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_m_203_, 0);
lean_dec(v_unused_245_);
v___x_224_ = v_m_203_;
v_isShared_225_ = v_isSharedCheck_243_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_m_203_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_243_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v_size_x27_227_; lean_object* v___x_228_; lean_object* v_buckets_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v_size_x27_227_ = lean_nat_add(v_size_206_, v___x_226_);
lean_dec(v_size_206_);
lean_inc(v_bkt_221_);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v_a_204_);
lean_ctor_set(v___x_228_, 1, v_b_205_);
lean_ctor_set(v___x_228_, 2, v_bkt_221_);
v_buckets_x27_229_ = lean_array_uset(v_buckets_207_, v___x_220_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(4u);
v___x_231_ = lean_nat_mul(v_size_x27_227_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(3u);
v___x_233_ = lean_nat_div(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_array_get_size(v_buckets_x27_229_);
v___x_235_ = lean_nat_dec_le(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
if (v___x_235_ == 0)
{
lean_object* v_val_236_; lean_object* v___x_238_; 
v_val_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_buckets_x27_229_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_val_236_);
lean_ctor_set(v___x_224_, 0, v_size_x27_227_);
v___x_238_ = v___x_224_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_val_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_241_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_buckets_x27_229_);
lean_ctor_set(v___x_224_, 0, v_size_x27_227_);
v___x_241_ = v___x_224_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_buckets_x27_229_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_dec(v_b_205_);
lean_dec(v_a_204_);
return v_m_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object* v_e_246_, lean_object* v_offset_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_t_250_; lean_object* v_b_251_; lean_object* v___y_252_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = l_Lean_Expr_looseBVarRange(v_e_246_);
v___x_259_ = lean_nat_dec_lt(v_offset_247_, v___x_258_);
lean_dec(v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_offset_247_);
lean_dec_ref(v_e_246_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_248_);
return v___x_261_;
}
else
{
lean_object* v_visited_262_; lean_object* v_bvars_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_visited_262_ = lean_ctor_get(v_a_248_, 0);
v_bvars_263_ = lean_ctor_get(v_a_248_, 1);
lean_inc_ref(v_e_246_);
lean_inc(v_offset_247_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_offset_247_);
lean_ctor_set(v___x_264_, 1, v_e_246_);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_visited_262_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_303_; 
lean_inc_ref(v_bvars_263_);
lean_inc_ref(v_visited_262_);
v_isSharedCheck_303_ = !lean_is_exclusive(v_a_248_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_304_ = lean_ctor_get(v_a_248_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_a_248_, 0);
lean_dec(v_unused_305_);
v___x_267_ = v_a_248_;
v_isShared_268_ = v_isSharedCheck_303_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_a_248_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_303_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_269_ = lean_box(0);
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_visited_262_, v___x_264_, v___x_269_);
lean_inc_ref(v_bvars_263_);
lean_inc_ref(v___x_270_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_bvars_263_);
v___x_272_ = v_reuseFailAlloc_302_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
switch(lean_obj_tag(v_e_246_))
{
case 0:
{
lean_object* v_deBruijnIndex_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v___x_272_);
v_deBruijnIndex_273_ = lean_ctor_get(v_e_246_, 0);
lean_inc(v_deBruijnIndex_273_);
lean_dec_ref(v_e_246_);
v___x_274_ = lean_nat_sub(v_deBruijnIndex_273_, v_offset_247_);
lean_dec(v_offset_247_);
lean_dec(v_deBruijnIndex_273_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_bvars_263_, v___x_274_, v___x_269_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_270_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_269_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
return v___x_277_;
}
case 5:
{
lean_object* v_fn_278_; lean_object* v_arg_279_; lean_object* v___x_280_; lean_object* v_snd_281_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
v_fn_278_ = lean_ctor_get(v_e_246_, 0);
lean_inc_ref(v_fn_278_);
v_arg_279_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_arg_279_);
lean_dec_ref(v_e_246_);
lean_inc(v_offset_247_);
v___x_280_ = l_Lean_Expr_CollectLooseBVars_main(v_fn_278_, v_offset_247_, v___x_272_);
v_snd_281_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_snd_281_);
lean_dec_ref(v___x_280_);
v_e_246_ = v_arg_279_;
v_a_248_ = v_snd_281_;
goto _start;
}
case 6:
{
lean_object* v_binderType_283_; lean_object* v_body_284_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
v_binderType_283_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_binderType_283_);
v_body_284_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_body_284_);
lean_dec_ref(v_e_246_);
v_t_250_ = v_binderType_283_;
v_b_251_ = v_body_284_;
v___y_252_ = v___x_272_;
goto v___jp_249_;
}
case 7:
{
lean_object* v_binderType_285_; lean_object* v_body_286_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
v_binderType_285_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_binderType_285_);
v_body_286_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_body_286_);
lean_dec_ref(v_e_246_);
v_t_250_ = v_binderType_285_;
v_b_251_ = v_body_286_;
v___y_252_ = v___x_272_;
goto v___jp_249_;
}
case 8:
{
lean_object* v_type_287_; lean_object* v_value_288_; lean_object* v_body_289_; lean_object* v___x_290_; lean_object* v_snd_291_; lean_object* v___x_292_; lean_object* v_snd_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
v_type_287_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_type_287_);
v_value_288_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_value_288_);
v_body_289_ = lean_ctor_get(v_e_246_, 3);
lean_inc_ref(v_body_289_);
lean_dec_ref(v_e_246_);
lean_inc_n(v_offset_247_, 2);
v___x_290_ = l_Lean_Expr_CollectLooseBVars_main(v_type_287_, v_offset_247_, v___x_272_);
v_snd_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_snd_291_);
lean_dec_ref(v___x_290_);
v___x_292_ = l_Lean_Expr_CollectLooseBVars_main(v_value_288_, v_offset_247_, v_snd_291_);
v_snd_293_ = lean_ctor_get(v___x_292_, 1);
lean_inc(v_snd_293_);
lean_dec_ref(v___x_292_);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_offset_247_, v___x_294_);
lean_dec(v_offset_247_);
v_e_246_ = v_body_289_;
v_offset_247_ = v___x_295_;
v_a_248_ = v_snd_293_;
goto _start;
}
case 10:
{
lean_object* v_expr_297_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
v_expr_297_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_expr_297_);
lean_dec_ref(v_e_246_);
v_e_246_ = v_expr_297_;
v_a_248_ = v___x_272_;
goto _start;
}
case 11:
{
lean_object* v_struct_299_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
v_struct_299_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_struct_299_);
lean_dec_ref(v_e_246_);
v_e_246_ = v_struct_299_;
v_a_248_ = v___x_272_;
goto _start;
}
default: 
{
lean_object* v___x_301_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_bvars_263_);
lean_dec(v_offset_247_);
lean_dec_ref(v_e_246_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_269_);
lean_ctor_set(v___x_301_, 1, v___x_272_);
return v___x_301_;
}
}
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v___x_264_);
lean_dec(v_offset_247_);
lean_dec_ref(v_e_246_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_a_248_);
return v___x_307_;
}
}
v___jp_249_:
{
lean_object* v___x_253_; lean_object* v_snd_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_inc(v_offset_247_);
v___x_253_ = l_Lean_Expr_CollectLooseBVars_main(v_t_250_, v_offset_247_, v___y_252_);
v_snd_254_ = lean_ctor_get(v___x_253_, 1);
lean_inc(v_snd_254_);
lean_dec_ref(v___x_253_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_offset_247_, v___x_255_);
lean_dec(v_offset_247_);
v_e_246_ = v_b_251_;
v_offset_247_ = v___x_256_;
v_a_248_ = v_snd_254_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object* v_00_u03b2_308_, lean_object* v_m_309_, lean_object* v_a_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_309_, v_a_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object* v_00_u03b2_312_, lean_object* v_m_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(v_00_u03b2_312_, v_m_313_, v_a_314_);
lean_dec_ref(v_a_314_);
lean_dec_ref(v_m_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object* v_00_u03b2_317_, lean_object* v_m_318_, lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_318_, v_a_319_, v_b_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object* v_00_u03b2_322_, lean_object* v_m_323_, lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_323_, v_a_324_, v_b_325_);
return v___x_326_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object* v_00_u03b2_327_, lean_object* v_a_328_, lean_object* v_x_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_328_, v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(v_00_u03b2_331_, v_a_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_a_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object* v_00_u03b2_336_, lean_object* v_data_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_data_337_);
return v___x_338_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object* v_00_u03b2_339_, lean_object* v_a_340_, lean_object* v_x_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object* v_00_u03b2_343_, lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(v_00_u03b2_343_, v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec(v_a_344_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5(lean_object* v_00_u03b2_348_, lean_object* v_data_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_data_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_351_, lean_object* v_i_352_, lean_object* v_source_353_, lean_object* v_target_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_i_352_, v_source_353_, v_target_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_356_, lean_object* v_i_357_, lean_object* v_source_358_, lean_object* v_target_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v_i_357_, v_source_358_, v_target_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_x_362_, v_x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_x_366_, v_x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_unsigned_to_nat(16u);
v___x_371_ = lean_mk_array(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__0, &l_Lean_Expr_collectLooseBVars___closed__0_once, _init_l_Lean_Expr_collectLooseBVars___closed__0);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_box(0);
v___x_376_ = lean_unsigned_to_nat(16u);
v___x_377_ = lean_mk_array(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__2, &l_Lean_Expr_collectLooseBVars___closed__2_once, _init_l_Lean_Expr_collectLooseBVars___closed__2);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__3, &l_Lean_Expr_collectLooseBVars___closed__3_once, _init_l_Lean_Expr_collectLooseBVars___closed__3);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object* v_e_383_, lean_object* v_offset_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = l_Lean_Expr_hasLooseBVars(v_e_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_offset_384_);
lean_dec_ref(v_e_383_);
v___x_386_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__1, &l_Lean_Expr_collectLooseBVars___closed__1_once, _init_l_Lean_Expr_collectLooseBVars___closed__1);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_snd_389_; lean_object* v_bvars_390_; 
v___x_387_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__4, &l_Lean_Expr_collectLooseBVars___closed__4_once, _init_l_Lean_Expr_collectLooseBVars___closed__4);
v___x_388_ = l_Lean_Expr_CollectLooseBVars_main(v_e_383_, v_offset_384_, v___x_387_);
v_snd_389_ = lean_ctor_get(v___x_388_, 1);
lean_inc(v_snd_389_);
lean_dec_ref(v___x_388_);
v_bvars_390_ = lean_ctor_get(v_snd_389_, 1);
lean_inc_ref(v_bvars_390_);
lean_dec(v_snd_389_);
return v_bvars_390_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
