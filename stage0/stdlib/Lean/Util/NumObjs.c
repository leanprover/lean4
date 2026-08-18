// Lean compiler output
// Module: Lean.Util.NumObjs
// Imports: public import Lean.Expr public import Lean.Util.PtrSet
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
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_NumObjs_main___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumObjs_main___closed__0;
static lean_once_cell_t l_Lean_Expr_NumObjs_main___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumObjs_main___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_NumObjs_0__Lean_Expr_numObjs_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; size_t v___x_44_; size_t v___x_45_; uint8_t v___x_46_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_ptr_addr(v_val_43_);
v___x_45_ = lean_ptr_addr(v_query_2_);
v___x_46_ = lean_usize_dec_eq(v___x_44_, v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
lean_dec(v_val_43_);
v___x_47_ = lean_array_get_size(v_keyArray_17_);
v___x_48_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_49_ = lean_nat_dec_lt(v___x_48_, v___x_47_);
if (v___x_49_ == 0)
{
lean_dec(v___x_48_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_48_;
goto _start;
}
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_52_ = lean_noption_get(v___x_41_);
v___x_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_53_, 0, v_x_5_);
lean_ctor_set(v___x_53_, 1, v_val_43_);
lean_ctor_set(v___x_53_, 2, v_val_52_);
return v___x_53_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg___boxed(lean_object* v_m_54_, lean_object* v_query_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_m_54_, v_query_55_, v_x_56_, v_x_57_, v_x_58_);
lean_dec_ref(v_query_55_);
lean_dec_ref(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object* v_m_60_, lean_object* v_query_61_){
_start:
{
lean_object* v_keyArray_62_; lean_object* v___x_63_; size_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_keyArray_62_ = lean_ctor_get(v_m_60_, 1);
v___x_63_ = lean_array_get_size(v_keyArray_62_);
v___x_64_ = lean_ptr_addr(v_query_61_);
v___x_65_ = lean_usize_to_uint64(v___x_64_);
v___x_66_ = 11ULL;
v___x_67_ = lean_uint64_mix_hash(v___x_65_, v___x_66_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_63_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v___x_79_ = lean_usize_to_nat(v___x_78_);
v___x_80_ = lean_box(0);
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_m_60_, v_query_61_, v___x_80_, v___x_63_, v___x_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg___boxed(lean_object* v_m_82_, lean_object* v_query_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_m_82_, v_query_83_);
lean_dec_ref(v_query_83_);
lean_dec_ref(v_m_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(lean_object* v_m_85_, lean_object* v_query_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_m_85_, v_query_86_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_index_88_; lean_object* v_key_89_; lean_object* v_value_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_index_88_ = lean_ctor_get(v___x_87_, 0);
v_key_89_ = lean_ctor_get(v___x_87_, 1);
v_value_90_ = lean_ctor_get(v___x_87_, 2);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_87_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_value_90_);
lean_inc(v_key_89_);
lean_inc(v_index_88_);
lean_dec(v___x_87_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_index_88_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_key_89_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_value_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v___x_98_; 
lean_dec(v___x_87_);
v___x_98_ = lean_box(1);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg___boxed(lean_object* v_m_99_, lean_object* v_query_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_m_99_, v_query_100_);
lean_dec_ref(v_query_100_);
lean_dec_ref(v_m_99_);
return v_res_101_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object* v_m_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_m_102_, v_a_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
uint8_t v___x_105_; 
lean_dec_ref_known(v___x_104_, 3);
v___x_105_ = 1;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg___boxed(lean_object* v_m_107_, lean_object* v_a_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_107_, v_a_108_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_m_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg(lean_object* v_b_111_, lean_object* v_acc_112_, lean_object* v_i_113_){
_start:
{
lean_object* v___y_115_; lean_object* v_keyArray_123_; lean_object* v_valueArray_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_keyArray_123_ = lean_ctor_get(v_b_111_, 1);
v_valueArray_124_ = lean_ctor_get(v_b_111_, 2);
v___x_125_ = lean_array_get_size(v_keyArray_123_);
v___x_126_ = lean_nat_dec_lt(v_i_113_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v_i_113_);
return v_acc_112_;
}
else
{
lean_object* v___x_127_; uint8_t v_isSome_128_; 
v___x_127_ = lean_array_fget_borrowed(v_keyArray_123_, v_i_113_);
v_isSome_128_ = lean_noption_is_some(v___x_127_);
if (v_isSome_128_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v___x_129_; uint8_t v_isSome_130_; 
v___x_129_ = lean_array_fget_borrowed(v_valueArray_124_, v_i_113_);
v_isSome_130_ = lean_noption_is_some(v___x_129_);
if (v_isSome_130_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v_val_131_; lean_object* v_val_132_; lean_object* v_i_134_; lean_object* v___x_139_; 
lean_inc(v___x_127_);
v_val_131_ = lean_noption_get(v___x_127_);
lean_inc(v___x_129_);
v_val_132_ = lean_noption_get(v___x_129_);
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_acc_112_, v_val_131_);
switch(lean_obj_tag(v___x_139_))
{
case 0:
{
lean_object* v_index_140_; lean_object* v_size_141_; lean_object* v___x_142_; 
v_index_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_index_140_);
lean_dec_ref_known(v___x_139_, 3);
v_size_141_ = lean_ctor_get(v_acc_112_, 0);
lean_inc(v_size_141_);
v___x_142_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_112_, v_size_141_, v_index_140_, v_val_131_, v_val_132_);
lean_dec(v_index_140_);
v___y_115_ = v___x_142_;
goto v___jp_114_;
}
case 1:
{
lean_object* v_index_143_; 
v_index_143_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_index_143_);
lean_dec_ref_known(v___x_139_, 1);
v_i_134_ = v_index_143_;
goto v___jp_133_;
}
default: 
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_112_, v___x_144_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_index_146_; 
v_index_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_index_146_);
lean_dec_ref_known(v___x_145_, 1);
v_i_134_ = v_index_146_;
goto v___jp_133_;
}
else
{
lean_dec(v_val_132_);
lean_dec(v_val_131_);
v___y_115_ = v_acc_112_;
goto v___jp_114_;
}
}
}
v___jp_133_:
{
lean_object* v_size_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_size_135_ = lean_ctor_get(v_acc_112_, 0);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_size_135_, v___x_136_);
v___x_138_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_112_, v___x_137_, v_i_134_, v_val_131_, v_val_132_);
lean_dec(v_i_134_);
v___y_115_ = v___x_138_;
goto v___jp_114_;
}
}
}
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_i_113_, v___x_116_);
lean_dec(v_i_113_);
v_acc_112_ = v___y_115_;
v_i_113_ = v___x_117_;
goto _start;
}
v___jp_119_:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_i_113_, v___x_120_);
lean_dec(v_i_113_);
v_i_113_ = v___x_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_147_, lean_object* v_acc_148_, lean_object* v_i_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg(v_b_147_, v_acc_148_, v_i_149_);
lean_dec_ref(v_b_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg(lean_object* v_init_151_, lean_object* v_b_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg(v_b_152_, v_init_151_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg___boxed(lean_object* v_init_155_, lean_object* v_b_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg(v_init_155_, v_b_156_);
lean_dec_ref(v_b_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(lean_object* v_m_158_){
_start:
{
lean_object* v_keyArray_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_cellCount_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_target_166_; lean_object* v___x_167_; 
v_keyArray_159_ = lean_ctor_get(v_m_158_, 1);
v___x_160_ = lean_array_get_size(v_keyArray_159_);
v___x_161_ = lean_unsigned_to_nat(2u);
v_cellCount_162_ = lean_nat_mul(v___x_160_, v___x_161_);
v___x_163_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_162_);
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_162_);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_162_);
v_target_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_166_, 0, v___x_163_);
lean_ctor_set(v_target_166_, 1, v___x_164_);
lean_ctor_set(v_target_166_, 2, v___x_165_);
v___x_167_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg(v_target_166_, v_m_158_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg___boxed(lean_object* v_m_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(v_m_168_);
lean_dec_ref(v_m_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object* v_e_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_d_173_; lean_object* v_b_174_; lean_object* v___y_175_; lean_object* v_visited_179_; lean_object* v_counter_180_; lean_object* v___y_182_; uint8_t v___x_209_; 
v_visited_179_ = lean_ctor_get(v_a_171_, 0);
v_counter_180_ = lean_ctor_get(v_a_171_, 1);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_visited_179_, v_e_170_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___y_212_; lean_object* v_i_213_; lean_object* v___y_219_; lean_object* v___y_229_; lean_object* v_i_230_; lean_object* v___x_245_; 
lean_inc(v_counter_180_);
lean_inc_ref(v_visited_179_);
lean_dec_ref(v_a_171_);
v___x_210_ = lean_box(0);
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_visited_179_, v_e_170_);
switch(lean_obj_tag(v___x_245_))
{
case 0:
{
lean_dec_ref_known(v___x_245_, 3);
v___y_182_ = v_visited_179_;
goto v___jp_181_;
}
case 1:
{
lean_object* v_index_246_; lean_object* v_size_247_; lean_object* v_keyArray_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_index_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_index_246_);
lean_dec_ref_known(v___x_245_, 1);
v_size_247_ = lean_ctor_get(v_visited_179_, 0);
v_keyArray_248_ = lean_ctor_get(v_visited_179_, 1);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_size_247_, v___x_249_);
v___x_251_ = lean_array_get_size(v_keyArray_248_);
v___x_252_ = lean_nat_dec_lt(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v___x_250_);
lean_dec(v_index_246_);
goto v___jp_235_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_253_ = lean_unsigned_to_nat(4u);
v___x_254_ = lean_nat_mul(v___x_250_, v___x_253_);
v___x_255_ = lean_unsigned_to_nat(3u);
v___x_256_ = lean_nat_mul(v___x_251_, v___x_255_);
v___x_257_ = lean_nat_dec_le(v___x_254_, v___x_256_);
lean_dec(v___x_256_);
lean_dec(v___x_254_);
if (v___x_257_ == 0)
{
lean_dec(v___x_250_);
lean_dec(v_index_246_);
goto v___jp_235_;
}
else
{
lean_object* v___x_258_; 
lean_inc_ref(v_e_170_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visited_179_, v___x_250_, v_index_246_, v_e_170_, v___x_210_);
lean_dec(v_index_246_);
v___y_182_ = v___x_258_;
goto v___jp_181_;
}
}
}
default: 
{
lean_object* v_size_259_; lean_object* v_keyArray_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_size_259_ = lean_ctor_get(v_visited_179_, 0);
v_keyArray_260_ = lean_ctor_get(v_visited_179_, 1);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_size_259_, v___x_261_);
v___x_263_ = lean_array_get_size(v_keyArray_260_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v___x_262_);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(v_visited_179_);
lean_dec_ref(v_visited_179_);
v___y_219_ = v___x_265_;
goto v___jp_218_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_266_ = lean_unsigned_to_nat(4u);
v___x_267_ = lean_nat_mul(v___x_262_, v___x_266_);
lean_dec(v___x_262_);
v___x_268_ = lean_unsigned_to_nat(3u);
v___x_269_ = lean_nat_mul(v___x_263_, v___x_268_);
v___x_270_ = lean_nat_dec_le(v___x_267_, v___x_269_);
lean_dec(v___x_269_);
lean_dec(v___x_267_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(v_visited_179_);
lean_dec_ref(v_visited_179_);
v___y_219_ = v___x_271_;
goto v___jp_218_;
}
else
{
v___y_219_ = v_visited_179_;
goto v___jp_218_;
}
}
}
}
v___jp_211_:
{
lean_object* v_size_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_size_214_ = lean_ctor_get(v___y_212_, 0);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_size_214_, v___x_215_);
lean_inc_ref(v_e_170_);
v___x_217_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_212_, v___x_216_, v_i_213_, v_e_170_, v___x_210_);
lean_dec(v_i_213_);
v___y_182_ = v___x_217_;
goto v___jp_181_;
}
v___jp_218_:
{
lean_object* v___x_220_; 
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v___y_219_, v_e_170_);
switch(lean_obj_tag(v___x_220_))
{
case 0:
{
lean_object* v_index_221_; lean_object* v_size_222_; lean_object* v___x_223_; 
v_index_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_index_221_);
lean_dec_ref_known(v___x_220_, 3);
v_size_222_ = lean_ctor_get(v___y_219_, 0);
lean_inc(v_size_222_);
lean_inc_ref(v_e_170_);
v___x_223_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_219_, v_size_222_, v_index_221_, v_e_170_, v___x_210_);
lean_dec(v_index_221_);
v___y_182_ = v___x_223_;
goto v___jp_181_;
}
case 1:
{
lean_object* v_index_224_; 
v_index_224_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_index_224_);
lean_dec_ref_known(v___x_220_, 1);
v___y_212_ = v___y_219_;
v_i_213_ = v_index_224_;
goto v___jp_211_;
}
default: 
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_219_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_index_227_; 
v_index_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_index_227_);
lean_dec_ref_known(v___x_226_, 1);
v___y_212_ = v___y_219_;
v_i_213_ = v_index_227_;
goto v___jp_211_;
}
else
{
v___y_182_ = v___y_219_;
goto v___jp_181_;
}
}
}
}
v___jp_228_:
{
lean_object* v_size_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_size_231_ = lean_ctor_get(v___y_229_, 0);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_size_231_, v___x_232_);
lean_inc_ref(v_e_170_);
v___x_234_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_229_, v___x_233_, v_i_230_, v_e_170_, v___x_210_);
lean_dec(v_i_230_);
v___y_182_ = v___x_234_;
goto v___jp_181_;
}
v___jp_235_:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(v_visited_179_);
lean_dec_ref(v_visited_179_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v___x_236_, v_e_170_);
switch(lean_obj_tag(v___x_237_))
{
case 0:
{
lean_object* v_index_238_; lean_object* v_size_239_; lean_object* v___x_240_; 
v_index_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_index_238_);
lean_dec_ref_known(v___x_237_, 3);
v_size_239_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_size_239_);
lean_inc_ref(v_e_170_);
v___x_240_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_236_, v_size_239_, v_index_238_, v_e_170_, v___x_210_);
lean_dec(v_index_238_);
v___y_182_ = v___x_240_;
goto v___jp_181_;
}
case 1:
{
lean_object* v_index_241_; 
v_index_241_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_index_241_);
lean_dec_ref_known(v___x_237_, 1);
v___y_229_ = v___x_236_;
v_i_230_ = v_index_241_;
goto v___jp_228_;
}
default: 
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_236_, v___x_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_index_244_; 
v_index_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_index_244_);
lean_dec_ref_known(v___x_243_, 1);
v___y_229_ = v___x_236_;
v_i_230_ = v_index_244_;
goto v___jp_228_;
}
else
{
v___y_182_ = v___x_236_;
goto v___jp_181_;
}
}
}
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref(v_e_170_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_a_171_);
return v___x_273_;
}
v___jp_172_:
{
lean_object* v___x_176_; lean_object* v_snd_177_; 
v___x_176_ = l_Lean_Expr_NumObjs_visit(v_d_173_, v___y_175_);
v_snd_177_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v___x_176_);
v_e_170_ = v_b_174_;
v_a_171_ = v_snd_177_;
goto _start;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_counter_180_, v___x_183_);
lean_dec(v_counter_180_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___y_182_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
switch(lean_obj_tag(v_e_170_))
{
case 7:
{
lean_object* v_binderType_186_; lean_object* v_body_187_; 
v_binderType_186_ = lean_ctor_get(v_e_170_, 1);
lean_inc_ref(v_binderType_186_);
v_body_187_ = lean_ctor_get(v_e_170_, 2);
lean_inc_ref(v_body_187_);
lean_dec_ref_known(v_e_170_, 3);
v_d_173_ = v_binderType_186_;
v_b_174_ = v_body_187_;
v___y_175_ = v___x_185_;
goto v___jp_172_;
}
case 6:
{
lean_object* v_binderType_188_; lean_object* v_body_189_; 
v_binderType_188_ = lean_ctor_get(v_e_170_, 1);
lean_inc_ref(v_binderType_188_);
v_body_189_ = lean_ctor_get(v_e_170_, 2);
lean_inc_ref(v_body_189_);
lean_dec_ref_known(v_e_170_, 3);
v_d_173_ = v_binderType_188_;
v_b_174_ = v_body_189_;
v___y_175_ = v___x_185_;
goto v___jp_172_;
}
case 10:
{
lean_object* v_expr_190_; 
v_expr_190_ = lean_ctor_get(v_e_170_, 1);
lean_inc_ref(v_expr_190_);
lean_dec_ref_known(v_e_170_, 2);
v_e_170_ = v_expr_190_;
v_a_171_ = v___x_185_;
goto _start;
}
case 8:
{
lean_object* v_type_192_; lean_object* v_value_193_; lean_object* v_body_194_; lean_object* v___x_195_; lean_object* v_snd_196_; lean_object* v___x_197_; lean_object* v_snd_198_; 
v_type_192_ = lean_ctor_get(v_e_170_, 1);
lean_inc_ref(v_type_192_);
v_value_193_ = lean_ctor_get(v_e_170_, 2);
lean_inc_ref(v_value_193_);
v_body_194_ = lean_ctor_get(v_e_170_, 3);
lean_inc_ref(v_body_194_);
lean_dec_ref_known(v_e_170_, 4);
v___x_195_ = l_Lean_Expr_NumObjs_visit(v_type_192_, v___x_185_);
v_snd_196_ = lean_ctor_get(v___x_195_, 1);
lean_inc(v_snd_196_);
lean_dec_ref(v___x_195_);
v___x_197_ = l_Lean_Expr_NumObjs_visit(v_value_193_, v_snd_196_);
v_snd_198_ = lean_ctor_get(v___x_197_, 1);
lean_inc(v_snd_198_);
lean_dec_ref(v___x_197_);
v_e_170_ = v_body_194_;
v_a_171_ = v_snd_198_;
goto _start;
}
case 5:
{
lean_object* v_fn_200_; lean_object* v_arg_201_; lean_object* v___x_202_; lean_object* v_snd_203_; 
v_fn_200_ = lean_ctor_get(v_e_170_, 0);
lean_inc_ref(v_fn_200_);
v_arg_201_ = lean_ctor_get(v_e_170_, 1);
lean_inc_ref(v_arg_201_);
lean_dec_ref_known(v_e_170_, 2);
v___x_202_ = l_Lean_Expr_NumObjs_visit(v_fn_200_, v___x_185_);
v_snd_203_ = lean_ctor_get(v___x_202_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v___x_202_);
v_e_170_ = v_arg_201_;
v_a_171_ = v_snd_203_;
goto _start;
}
case 11:
{
lean_object* v_struct_205_; 
v_struct_205_ = lean_ctor_get(v_e_170_, 2);
lean_inc_ref(v_struct_205_);
lean_dec_ref_known(v_e_170_, 3);
v_e_170_ = v_struct_205_;
v_a_171_ = v___x_185_;
goto _start;
}
default: 
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v_e_170_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_185_);
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(lean_object* v_00_u03b2_274_, lean_object* v_m_275_, lean_object* v_a_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_275_, v_a_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___boxed(lean_object* v_00_u03b2_278_, lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(v_00_u03b2_278_, v_m_279_, v_a_280_);
lean_dec_ref(v_a_280_);
lean_dec_ref(v_m_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1(lean_object* v_00_u03b2_283_, lean_object* v_m_284_, lean_object* v_query_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_m_284_, v_query_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1___boxed(lean_object* v_00_u03b2_287_, lean_object* v_m_288_, lean_object* v_query_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1(v_00_u03b2_287_, v_m_288_, v_query_289_);
lean_dec_ref(v_query_289_);
lean_dec_ref(v_m_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2(lean_object* v_00_u03b2_291_, lean_object* v_m_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___redArg(v_m_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2___boxed(lean_object* v_00_u03b2_294_, lean_object* v_m_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2(v_00_u03b2_294_, v_m_295_);
lean_dec_ref(v_m_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_query_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_m_298_, v_query_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_query_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(v_00_u03b2_301_, v_m_302_, v_query_303_);
lean_dec_ref(v_query_303_);
lean_dec_ref(v_m_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(lean_object* v_00_u03b2_305_, lean_object* v_m_306_, lean_object* v_query_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_m_306_, v_query_307_, v_x_308_, v_x_309_, v_x_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_313_, lean_object* v_m_314_, lean_object* v_query_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(v_00_u03b2_313_, v_m_314_, v_query_315_, v_x_316_, v_x_317_, v_x_318_, v_x_319_);
lean_dec_ref(v_query_315_);
lean_dec_ref(v_m_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4(lean_object* v_00_u03b2_321_, lean_object* v_init_322_, lean_object* v_b_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___redArg(v_init_322_, v_b_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4___boxed(lean_object* v_00_u03b2_325_, lean_object* v_init_326_, lean_object* v_b_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4(v_00_u03b2_325_, v_init_326_, v_b_327_);
lean_dec_ref(v_b_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_329_, lean_object* v_b_330_, lean_object* v_acc_331_, lean_object* v_i_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___redArg(v_b_330_, v_acc_331_, v_i_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_334_, lean_object* v_b_335_, lean_object* v_acc_336_, lean_object* v_i_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumObjs_visit_spec__2_spec__4_spec__5(v_00_u03b2_334_, v_b_335_, v_acc_336_, v_i_337_);
lean_dec_ref(v_b_335_);
return v_res_338_;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(64u);
v___x_340_ = l_Lean_mkPtrSet___redArg(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_obj_once(&l_Lean_Expr_NumObjs_main___closed__0, &l_Lean_Expr_NumObjs_main___closed__0_once, _init_l_Lean_Expr_NumObjs_main___closed__0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object* v_e_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_snd_347_; lean_object* v_counter_348_; 
v___x_345_ = lean_obj_once(&l_Lean_Expr_NumObjs_main___closed__1, &l_Lean_Expr_NumObjs_main___closed__1_once, _init_l_Lean_Expr_NumObjs_main___closed__1);
v___x_346_ = l_Lean_Expr_NumObjs_visit(v_e_344_, v___x_345_);
v_snd_347_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_snd_347_);
lean_dec_ref(v___x_346_);
v_counter_348_ = lean_ctor_get(v_snd_347_, 1);
lean_inc(v_counter_348_);
lean_dec(v_snd_347_);
return v_counter_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumObjs_0__Lean_Expr_numObjs_unsafe__1(lean_object* v_e_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Expr_NumObjs_main(v_e_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs(lean_object* v_e_351_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = l_Lean_Expr_NumObjs_main(v_e_351_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs___boxed(lean_object* v_e_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Expr_numObjs(v_e_355_);
return v_res_357_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_NumObjs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_NumObjs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_NumObjs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_NumObjs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_NumObjs(builtin);
}
#ifdef __cplusplus
}
#endif
