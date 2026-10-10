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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_14_;
v_res_14_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_14_;
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(lean_object* v_m_19_, lean_object* v_a_20_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_19_ = stack[0].m_obj;
lean_object* v_a_20_ = stack[1].m_obj;
uint8_t v_res_41_;
v_res_41_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_19_, v_a_20_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(lean_object* v_m_42_, lean_object* v_a_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_42_, v_a_43_);
lean_dec_ref(v_a_43_);
lean_dec_ref(v_m_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
return v_x_46_;
}
else
{
lean_object* v_key_48_; lean_object* v_value_49_; lean_object* v_tail_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_77_; 
v_key_48_ = lean_ctor_get(v_x_47_, 0);
v_value_49_ = lean_ctor_get(v_x_47_, 1);
v_tail_50_ = lean_ctor_get(v_x_47_, 2);
v_isSharedCheck_77_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_77_ == 0)
{
v___x_52_ = v_x_47_;
v_isShared_53_ = v_isSharedCheck_77_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_tail_50_);
lean_inc(v_value_49_);
lean_inc(v_key_48_);
lean_dec(v_x_47_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_77_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_fst_54_; lean_object* v_snd_55_; lean_object* v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; uint64_t v___x_61_; uint64_t v_fold_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; size_t v___x_69_; size_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v_fst_54_ = lean_ctor_get(v_key_48_, 0);
v_snd_55_ = lean_ctor_get(v_key_48_, 1);
v___x_56_ = lean_array_get_size(v_x_46_);
v___x_57_ = lean_uint64_of_nat(v_fst_54_);
v___x_58_ = l_Lean_Expr_hash(v_snd_55_);
v___x_59_ = lean_uint64_mix_hash(v___x_57_, v___x_58_);
v___x_60_ = 32ULL;
v___x_61_ = lean_uint64_shift_right(v___x_59_, v___x_60_);
v_fold_62_ = lean_uint64_xor(v___x_59_, v___x_61_);
v___x_63_ = 16ULL;
v___x_64_ = lean_uint64_shift_right(v_fold_62_, v___x_63_);
v___x_65_ = lean_uint64_xor(v_fold_62_, v___x_64_);
v___x_66_ = lean_uint64_to_usize(v___x_65_);
v___x_67_ = lean_usize_of_nat(v___x_56_);
v___x_68_ = ((size_t)1ULL);
v___x_69_ = lean_usize_sub(v___x_67_, v___x_68_);
v___x_70_ = lean_usize_land(v___x_66_, v___x_69_);
v___x_71_ = lean_array_uget_borrowed(v_x_46_, v___x_70_);
lean_inc(v___x_71_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 2, v___x_71_);
v___x_73_ = v___x_52_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_key_48_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_value_49_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; 
v___x_74_ = lean_array_uset(v_x_46_, v___x_70_, v___x_73_);
v_x_46_ = v___x_74_;
v_x_47_ = v_tail_50_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(lean_object* v_i_78_, lean_object* v_source_79_, lean_object* v_target_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_array_get_size(v_source_79_);
v___x_82_ = lean_nat_dec_lt(v_i_78_, v___x_81_);
if (v___x_82_ == 0)
{
lean_dec_ref(v_source_79_);
lean_dec(v_i_78_);
return v_target_80_;
}
else
{
lean_object* v_es_83_; lean_object* v___x_84_; lean_object* v_source_85_; lean_object* v_target_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_es_83_ = lean_array_fget(v_source_79_, v_i_78_);
v___x_84_ = lean_box(0);
v_source_85_ = lean_array_fset(v_source_79_, v_i_78_, v___x_84_);
v_target_86_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_target_80_, v_es_83_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_78_, v___x_87_);
lean_dec(v_i_78_);
v_i_78_ = v___x_88_;
v_source_79_ = v_source_85_;
v_target_80_ = v_target_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(lean_object* v_data_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_nbuckets_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_91_ = lean_array_get_size(v_data_90_);
v___x_92_ = lean_unsigned_to_nat(2u);
v_nbuckets_93_ = lean_nat_mul(v___x_91_, v___x_92_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_box(0);
v___x_96_ = lean_mk_array(v_nbuckets_93_, v___x_95_);
v___x_97_ = lean_array_propagate_mark(v_data_90_, v___x_96_);
v___x_98_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v___x_94_, v_data_90_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(lean_object* v_m_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_size_102_; lean_object* v_buckets_103_; lean_object* v_fst_104_; lean_object* v_snd_105_; lean_object* v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v_fold_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; lean_object* v_bkt_121_; uint8_t v___x_122_; 
v_size_102_ = lean_ctor_get(v_m_99_, 0);
v_buckets_103_ = lean_ctor_get(v_m_99_, 1);
v_fst_104_ = lean_ctor_get(v_a_100_, 0);
v_snd_105_ = lean_ctor_get(v_a_100_, 1);
v___x_106_ = lean_array_get_size(v_buckets_103_);
v___x_107_ = lean_uint64_of_nat(v_fst_104_);
v___x_108_ = l_Lean_Expr_hash(v_snd_105_);
v___x_109_ = lean_uint64_mix_hash(v___x_107_, v___x_108_);
v___x_110_ = 32ULL;
v___x_111_ = lean_uint64_shift_right(v___x_109_, v___x_110_);
v_fold_112_ = lean_uint64_xor(v___x_109_, v___x_111_);
v___x_113_ = 16ULL;
v___x_114_ = lean_uint64_shift_right(v_fold_112_, v___x_113_);
v___x_115_ = lean_uint64_xor(v_fold_112_, v___x_114_);
v___x_116_ = lean_uint64_to_usize(v___x_115_);
v___x_117_ = lean_usize_of_nat(v___x_106_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_sub(v___x_117_, v___x_118_);
v___x_120_ = lean_usize_land(v___x_116_, v___x_119_);
v_bkt_121_ = lean_array_uget_borrowed(v_buckets_103_, v___x_120_);
v___x_122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_100_, v_bkt_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_143_; 
lean_inc_ref(v_buckets_103_);
lean_inc(v_size_102_);
v_isSharedCheck_143_ = !lean_is_exclusive(v_m_99_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; lean_object* v_unused_145_; 
v_unused_144_ = lean_ctor_get(v_m_99_, 1);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_m_99_, 0);
lean_dec(v_unused_145_);
v___x_124_ = v_m_99_;
v_isShared_125_ = v_isSharedCheck_143_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_m_99_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_143_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v_size_x27_127_; lean_object* v___x_128_; lean_object* v_buckets_x27_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v_size_x27_127_ = lean_nat_add(v_size_102_, v___x_126_);
lean_dec(v_size_102_);
lean_inc(v_bkt_121_);
v___x_128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_128_, 0, v_a_100_);
lean_ctor_set(v___x_128_, 1, v_b_101_);
lean_ctor_set(v___x_128_, 2, v_bkt_121_);
v_buckets_x27_129_ = lean_array_uset(v_buckets_103_, v___x_120_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(4u);
v___x_131_ = lean_nat_mul(v_size_x27_127_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(3u);
v___x_133_ = lean_nat_div(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_array_get_size(v_buckets_x27_129_);
v___x_135_ = lean_nat_dec_le(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
if (v___x_135_ == 0)
{
lean_object* v_val_136_; lean_object* v___x_138_; 
v_val_136_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_buckets_x27_129_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v_val_136_);
lean_ctor_set(v___x_124_, 0, v_size_x27_127_);
v___x_138_ = v___x_124_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_size_x27_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_val_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
else
{
lean_object* v___x_141_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v_buckets_x27_129_);
lean_ctor_set(v___x_124_, 0, v_size_x27_127_);
v___x_141_ = v___x_124_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_size_x27_127_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_buckets_x27_129_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
else
{
lean_dec(v_b_101_);
lean_dec_ref(v_a_100_);
return v_m_99_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
return v_x_146_;
}
else
{
lean_object* v_key_148_; lean_object* v_value_149_; lean_object* v_tail_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_173_; 
v_key_148_ = lean_ctor_get(v_x_147_, 0);
v_value_149_ = lean_ctor_get(v_x_147_, 1);
v_tail_150_ = lean_ctor_get(v_x_147_, 2);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_173_ == 0)
{
v___x_152_ = v_x_147_;
v_isShared_153_ = v_isSharedCheck_173_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_tail_150_);
lean_inc(v_value_149_);
lean_inc(v_key_148_);
lean_dec(v_x_147_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_173_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v_fold_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_154_ = lean_array_get_size(v_x_146_);
v___x_155_ = lean_uint64_of_nat(v_key_148_);
v___x_156_ = 32ULL;
v___x_157_ = lean_uint64_shift_right(v___x_155_, v___x_156_);
v_fold_158_ = lean_uint64_xor(v___x_155_, v___x_157_);
v___x_159_ = 16ULL;
v___x_160_ = lean_uint64_shift_right(v_fold_158_, v___x_159_);
v___x_161_ = lean_uint64_xor(v_fold_158_, v___x_160_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = lean_usize_of_nat(v___x_154_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_sub(v___x_163_, v___x_164_);
v___x_166_ = lean_usize_land(v___x_162_, v___x_165_);
v___x_167_ = lean_array_uget_borrowed(v_x_146_, v___x_166_);
lean_inc(v___x_167_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 2, v___x_167_);
v___x_169_ = v___x_152_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_key_148_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_value_149_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v___x_167_);
v___x_169_ = v_reuseFailAlloc_172_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_array_uset(v_x_146_, v___x_166_, v___x_169_);
v_x_146_ = v___x_170_;
v_x_147_ = v_tail_150_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(lean_object* v_i_174_, lean_object* v_source_175_, lean_object* v_target_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_array_get_size(v_source_175_);
v___x_178_ = lean_nat_dec_lt(v_i_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec_ref(v_source_175_);
lean_dec(v_i_174_);
return v_target_176_;
}
else
{
lean_object* v_es_179_; lean_object* v___x_180_; lean_object* v_source_181_; lean_object* v_target_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_es_179_ = lean_array_fget(v_source_175_, v_i_174_);
v___x_180_ = lean_box(0);
v_source_181_ = lean_array_fset(v_source_175_, v_i_174_, v___x_180_);
v_target_182_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_target_176_, v_es_179_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_i_174_, v___x_183_);
lean_dec(v_i_174_);
v_i_174_ = v___x_184_;
v_source_175_ = v_source_181_;
v_target_176_ = v_target_182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(lean_object* v_data_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_nbuckets_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_187_ = lean_array_get_size(v_data_186_);
v___x_188_ = lean_unsigned_to_nat(2u);
v_nbuckets_189_ = lean_nat_mul(v___x_187_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_box(0);
v___x_192_ = lean_mk_array(v_nbuckets_189_, v___x_191_);
v___x_193_ = lean_array_propagate_mark(v_data_186_, v___x_192_);
v___x_194_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v___x_190_, v_data_186_, v___x_193_);
return v___x_194_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object* v_a_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
else
{
lean_object* v_key_198_; lean_object* v_tail_199_; uint8_t v___x_200_; 
v_key_198_ = lean_ctor_get(v_x_196_, 0);
v_tail_199_ = lean_ctor_get(v_x_196_, 2);
v___x_200_ = lean_nat_dec_eq(v_key_198_, v_a_195_);
if (v___x_200_ == 0)
{
v_x_196_ = v_tail_199_;
goto _start;
}
else
{
return v___x_200_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_195_ = stack[0].m_obj;
lean_object* v_x_196_ = stack[1].m_obj;
uint8_t v_res_202_;
v_res_202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_195_, v_x_196_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_203_, v_x_204_);
lean_dec(v_x_204_);
lean_dec(v_a_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object* v_m_207_, lean_object* v_a_208_, lean_object* v_b_209_){
_start:
{
lean_object* v_size_210_; lean_object* v_buckets_211_; lean_object* v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v_fold_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v_bkt_225_; uint8_t v___x_226_; 
v_size_210_ = lean_ctor_get(v_m_207_, 0);
v_buckets_211_ = lean_ctor_get(v_m_207_, 1);
v___x_212_ = lean_array_get_size(v_buckets_211_);
v___x_213_ = lean_uint64_of_nat(v_a_208_);
v___x_214_ = 32ULL;
v___x_215_ = lean_uint64_shift_right(v___x_213_, v___x_214_);
v_fold_216_ = lean_uint64_xor(v___x_213_, v___x_215_);
v___x_217_ = 16ULL;
v___x_218_ = lean_uint64_shift_right(v_fold_216_, v___x_217_);
v___x_219_ = lean_uint64_xor(v_fold_216_, v___x_218_);
v___x_220_ = lean_uint64_to_usize(v___x_219_);
v___x_221_ = lean_usize_of_nat(v___x_212_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_sub(v___x_221_, v___x_222_);
v___x_224_ = lean_usize_land(v___x_220_, v___x_223_);
v_bkt_225_ = lean_array_uget_borrowed(v_buckets_211_, v___x_224_);
v___x_226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_208_, v_bkt_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_247_; 
lean_inc_ref(v_buckets_211_);
lean_inc(v_size_210_);
v_isSharedCheck_247_ = !lean_is_exclusive(v_m_207_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_248_ = lean_ctor_get(v_m_207_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_m_207_, 0);
lean_dec(v_unused_249_);
v___x_228_ = v_m_207_;
v_isShared_229_ = v_isSharedCheck_247_;
goto v_resetjp_227_;
}
else
{
lean_dec(v_m_207_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_247_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v_size_x27_231_; lean_object* v___x_232_; lean_object* v_buckets_x27_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v_size_x27_231_ = lean_nat_add(v_size_210_, v___x_230_);
lean_dec(v_size_210_);
lean_inc(v_bkt_225_);
v___x_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_232_, 0, v_a_208_);
lean_ctor_set(v___x_232_, 1, v_b_209_);
lean_ctor_set(v___x_232_, 2, v_bkt_225_);
v_buckets_x27_233_ = lean_array_uset(v_buckets_211_, v___x_224_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(4u);
v___x_235_ = lean_nat_mul(v_size_x27_231_, v___x_234_);
v___x_236_ = lean_unsigned_to_nat(3u);
v___x_237_ = lean_nat_div(v___x_235_, v___x_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_array_get_size(v_buckets_x27_233_);
v___x_239_ = lean_nat_dec_le(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
if (v___x_239_ == 0)
{
lean_object* v_val_240_; lean_object* v___x_242_; 
v_val_240_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_buckets_x27_233_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v_val_240_);
lean_ctor_set(v___x_228_, 0, v_size_x27_231_);
v___x_242_ = v___x_228_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_size_x27_231_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_val_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
else
{
lean_object* v___x_245_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v_buckets_x27_233_);
lean_ctor_set(v___x_228_, 0, v_size_x27_231_);
v___x_245_ = v___x_228_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_size_x27_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_buckets_x27_233_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_dec(v_b_209_);
lean_dec(v_a_208_);
return v_m_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object* v_e_250_, lean_object* v_offset_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_t_254_; lean_object* v_b_255_; lean_object* v___y_256_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = l_Lean_Expr_looseBVarRange(v_e_250_);
v___x_263_ = lean_nat_dec_lt(v_offset_251_, v___x_262_);
lean_dec(v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_offset_251_);
lean_dec_ref(v_e_250_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_252_);
return v___x_265_;
}
else
{
lean_object* v_visited_266_; lean_object* v_bvars_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_visited_266_ = lean_ctor_get(v_a_252_, 0);
v_bvars_267_ = lean_ctor_get(v_a_252_, 1);
lean_inc_ref(v_e_250_);
lean_inc(v_offset_251_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_offset_251_);
lean_ctor_set(v___x_268_, 1, v_e_250_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_visited_266_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_307_; 
lean_inc_ref(v_bvars_267_);
lean_inc_ref(v_visited_266_);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; 
v_unused_308_ = lean_ctor_get(v_a_252_, 1);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_a_252_, 0);
lean_dec(v_unused_309_);
v___x_271_ = v_a_252_;
v_isShared_272_ = v_isSharedCheck_307_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_a_252_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_307_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_box(0);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_visited_266_, v___x_268_, v___x_273_);
lean_inc_ref(v_bvars_267_);
lean_inc_ref(v___x_274_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_bvars_267_);
v___x_276_ = v_reuseFailAlloc_306_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
switch(lean_obj_tag(v_e_250_))
{
case 0:
{
lean_object* v_deBruijnIndex_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v___x_276_);
v_deBruijnIndex_277_ = lean_ctor_get(v_e_250_, 0);
lean_inc(v_deBruijnIndex_277_);
lean_dec_ref_known(v_e_250_, 1);
v___x_278_ = lean_nat_sub(v_deBruijnIndex_277_, v_offset_251_);
lean_dec(v_offset_251_);
lean_dec(v_deBruijnIndex_277_);
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_bvars_267_, v___x_278_, v___x_273_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_274_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_273_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
case 5:
{
lean_object* v_fn_282_; lean_object* v_arg_283_; lean_object* v___x_284_; lean_object* v_snd_285_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
v_fn_282_ = lean_ctor_get(v_e_250_, 0);
lean_inc_ref(v_fn_282_);
v_arg_283_ = lean_ctor_get(v_e_250_, 1);
lean_inc_ref(v_arg_283_);
lean_dec_ref_known(v_e_250_, 2);
lean_inc(v_offset_251_);
v___x_284_ = l_Lean_Expr_CollectLooseBVars_main(v_fn_282_, v_offset_251_, v___x_276_);
v_snd_285_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_snd_285_);
lean_dec_ref(v___x_284_);
v_e_250_ = v_arg_283_;
v_a_252_ = v_snd_285_;
goto _start;
}
case 6:
{
lean_object* v_binderType_287_; lean_object* v_body_288_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
v_binderType_287_ = lean_ctor_get(v_e_250_, 1);
lean_inc_ref(v_binderType_287_);
v_body_288_ = lean_ctor_get(v_e_250_, 2);
lean_inc_ref(v_body_288_);
lean_dec_ref_known(v_e_250_, 3);
v_t_254_ = v_binderType_287_;
v_b_255_ = v_body_288_;
v___y_256_ = v___x_276_;
goto v___jp_253_;
}
case 7:
{
lean_object* v_binderType_289_; lean_object* v_body_290_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
v_binderType_289_ = lean_ctor_get(v_e_250_, 1);
lean_inc_ref(v_binderType_289_);
v_body_290_ = lean_ctor_get(v_e_250_, 2);
lean_inc_ref(v_body_290_);
lean_dec_ref_known(v_e_250_, 3);
v_t_254_ = v_binderType_289_;
v_b_255_ = v_body_290_;
v___y_256_ = v___x_276_;
goto v___jp_253_;
}
case 8:
{
lean_object* v_type_291_; lean_object* v_value_292_; lean_object* v_body_293_; lean_object* v___x_294_; lean_object* v_snd_295_; lean_object* v___x_296_; lean_object* v_snd_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
v_type_291_ = lean_ctor_get(v_e_250_, 1);
lean_inc_ref(v_type_291_);
v_value_292_ = lean_ctor_get(v_e_250_, 2);
lean_inc_ref(v_value_292_);
v_body_293_ = lean_ctor_get(v_e_250_, 3);
lean_inc_ref(v_body_293_);
lean_dec_ref_known(v_e_250_, 4);
lean_inc_n(v_offset_251_, 2);
v___x_294_ = l_Lean_Expr_CollectLooseBVars_main(v_type_291_, v_offset_251_, v___x_276_);
v_snd_295_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_snd_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = l_Lean_Expr_CollectLooseBVars_main(v_value_292_, v_offset_251_, v_snd_295_);
v_snd_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_snd_297_);
lean_dec_ref(v___x_296_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_offset_251_, v___x_298_);
lean_dec(v_offset_251_);
v_e_250_ = v_body_293_;
v_offset_251_ = v___x_299_;
v_a_252_ = v_snd_297_;
goto _start;
}
case 10:
{
lean_object* v_expr_301_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
v_expr_301_ = lean_ctor_get(v_e_250_, 1);
lean_inc_ref(v_expr_301_);
lean_dec_ref_known(v_e_250_, 2);
v_e_250_ = v_expr_301_;
v_a_252_ = v___x_276_;
goto _start;
}
case 11:
{
lean_object* v_struct_303_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
v_struct_303_ = lean_ctor_get(v_e_250_, 2);
lean_inc_ref(v_struct_303_);
lean_dec_ref_known(v_e_250_, 3);
v_e_250_ = v_struct_303_;
v_a_252_ = v___x_276_;
goto _start;
}
default: 
{
lean_object* v___x_305_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_bvars_267_);
lean_dec(v_offset_251_);
lean_dec_ref(v_e_250_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_273_);
lean_ctor_set(v___x_305_, 1, v___x_276_);
return v___x_305_;
}
}
}
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref_known(v___x_268_, 2);
lean_dec(v_offset_251_);
lean_dec_ref(v_e_250_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_252_);
return v___x_311_;
}
}
v___jp_253_:
{
lean_object* v___x_257_; lean_object* v_snd_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_inc(v_offset_251_);
v___x_257_ = l_Lean_Expr_CollectLooseBVars_main(v_t_254_, v_offset_251_, v___y_256_);
v_snd_258_ = lean_ctor_get(v___x_257_, 1);
lean_inc(v_snd_258_);
lean_dec_ref(v___x_257_);
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_offset_251_, v___x_259_);
lean_dec(v_offset_251_);
v_e_250_ = v_b_255_;
v_offset_251_ = v___x_260_;
v_a_252_ = v_snd_258_;
goto _start;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object* v_00_u03b2_312_, lean_object* v_m_313_, lean_object* v_a_314_){
_start:
{
uint8_t v___x_315_; 
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_313_, v_a_314_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_313_ = stack[1].m_obj;
lean_object* v_a_314_ = stack[2].m_obj;
uint8_t v_res_316_;
v_res_316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_box(0), v_m_313_, v_a_314_);
stack->m_num = v_res_316_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object* v_00_u03b2_317_, lean_object* v_m_318_, lean_object* v_a_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(v_00_u03b2_317_, v_m_318_, v_a_319_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_m_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object* v_00_u03b2_322_, lean_object* v_m_323_, lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_323_, v_a_324_, v_b_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_a_329_, lean_object* v_b_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_328_, v_a_329_, v_b_330_);
return v___x_331_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object* v_00_u03b2_332_, lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_333_ = stack[1].m_obj;
lean_object* v_x_334_ = stack[2].m_obj;
uint8_t v_res_336_;
v_res_336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_box(0), v_a_333_, v_x_334_);
stack->m_num = v_res_336_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object* v_00_u03b2_337_, lean_object* v_a_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(v_00_u03b2_337_, v_a_338_, v_x_339_);
lean_dec(v_x_339_);
lean_dec_ref(v_a_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object* v_00_u03b2_342_, lean_object* v_data_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_data_343_);
return v___x_344_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object* v_00_u03b2_345_, lean_object* v_a_346_, lean_object* v_x_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_346_ = stack[1].m_obj;
lean_object* v_x_347_ = stack[2].m_obj;
uint8_t v_res_349_;
v_res_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_box(0), v_a_346_, v_x_347_);
stack->m_num = v_res_349_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object* v_00_u03b2_350_, lean_object* v_a_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(v_00_u03b2_350_, v_a_351_, v_x_352_);
lean_dec(v_x_352_);
lean_dec(v_a_351_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5(lean_object* v_00_u03b2_355_, lean_object* v_data_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_data_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_358_, lean_object* v_i_359_, lean_object* v_source_360_, lean_object* v_target_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_i_359_, v_source_360_, v_target_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_363_, lean_object* v_i_364_, lean_object* v_source_365_, lean_object* v_target_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v_i_364_, v_source_365_, v_target_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_x_369_, v_x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_x_373_, v_x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__0(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_unsigned_to_nat(16u);
v___x_378_ = lean_mk_array(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__0, &l_Lean_Expr_collectLooseBVars___closed__0_once, _init_l_Lean_Expr_collectLooseBVars___closed__0);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_box(0);
v___x_383_ = lean_unsigned_to_nat(16u);
v___x_384_ = lean_mk_array(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__3(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__2, &l_Lean_Expr_collectLooseBVars___closed__2_once, _init_l_Lean_Expr_collectLooseBVars___closed__2);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__4(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__3, &l_Lean_Expr_collectLooseBVars___closed__3_once, _init_l_Lean_Expr_collectLooseBVars___closed__3);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object* v_e_390_, lean_object* v_offset_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Expr_hasLooseBVars(v_e_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v_offset_391_);
lean_dec_ref(v_e_390_);
v___x_393_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__1, &l_Lean_Expr_collectLooseBVars___closed__1_once, _init_l_Lean_Expr_collectLooseBVars___closed__1);
return v___x_393_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_snd_396_; lean_object* v_bvars_397_; 
v___x_394_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__4, &l_Lean_Expr_collectLooseBVars___closed__4_once, _init_l_Lean_Expr_collectLooseBVars___closed__4);
v___x_395_ = l_Lean_Expr_CollectLooseBVars_main(v_e_390_, v_offset_391_, v___x_394_);
v_snd_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc(v_snd_396_);
lean_dec_ref(v___x_395_);
v_bvars_397_ = lean_ctor_get(v_snd_396_, 1);
lean_inc_ref(v_bvars_397_);
lean_dec(v_snd_396_);
return v_bvars_397_;
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
