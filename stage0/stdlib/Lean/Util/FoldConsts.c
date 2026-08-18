// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: public import Lean.Util.PtrSet public import Lean.Declaration
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
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_NameSet_ofList(lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_getUsedConstants___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_getUsedConstants___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_getUsedConstants___closed__0 = (const lean_object*)&l_Lean_Expr_getUsedConstants___closed__0_value;
static const lean_array_object l_Lean_Expr_getUsedConstants___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_getUsedConstants___closed__1 = (const lean_object*)&l_Lean_Expr_getUsedConstants___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_getUsedConstantsAsSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_getUsedConstantsAsSet___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_getUsedConstantsAsSet___closed__0 = (const lean_object*)&l_Lean_Expr_getUsedConstantsAsSet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg___boxed(lean_object* v_m_54_, lean_object* v_query_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_m_54_, v_query_55_, v_x_56_, v_x_57_, v_x_58_);
lean_dec_ref(v_query_55_);
lean_dec_ref(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object* v_m_60_, lean_object* v_query_61_){
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
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_m_60_, v_query_61_, v___x_80_, v___x_63_, v___x_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg___boxed(lean_object* v_m_82_, lean_object* v_query_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_m_82_, v_query_83_);
lean_dec_ref(v_query_83_);
lean_dec_ref(v_m_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg(lean_object* v_b_85_, lean_object* v_acc_86_, lean_object* v_i_87_){
_start:
{
lean_object* v___y_89_; lean_object* v_keyArray_97_; lean_object* v_valueArray_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_keyArray_97_ = lean_ctor_get(v_b_85_, 1);
v_valueArray_98_ = lean_ctor_get(v_b_85_, 2);
v___x_99_ = lean_array_get_size(v_keyArray_97_);
v___x_100_ = lean_nat_dec_lt(v_i_87_, v___x_99_);
if (v___x_100_ == 0)
{
lean_dec(v_i_87_);
return v_acc_86_;
}
else
{
lean_object* v___x_101_; uint8_t v_isSome_102_; 
v___x_101_ = lean_array_fget_borrowed(v_keyArray_97_, v_i_87_);
v_isSome_102_ = lean_noption_is_some(v___x_101_);
if (v_isSome_102_ == 0)
{
goto v___jp_93_;
}
else
{
lean_object* v___x_103_; uint8_t v_isSome_104_; 
v___x_103_ = lean_array_fget_borrowed(v_valueArray_98_, v_i_87_);
v_isSome_104_ = lean_noption_is_some(v___x_103_);
if (v_isSome_104_ == 0)
{
goto v___jp_93_;
}
else
{
lean_object* v_val_105_; lean_object* v_val_106_; lean_object* v_i_108_; lean_object* v___x_113_; 
lean_inc(v___x_101_);
v_val_105_ = lean_noption_get(v___x_101_);
lean_inc(v___x_103_);
v_val_106_ = lean_noption_get(v___x_103_);
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_acc_86_, v_val_105_);
switch(lean_obj_tag(v___x_113_))
{
case 0:
{
lean_object* v_index_114_; lean_object* v_size_115_; lean_object* v___x_116_; 
v_index_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_index_114_);
lean_dec_ref_known(v___x_113_, 3);
v_size_115_ = lean_ctor_get(v_acc_86_, 0);
lean_inc(v_size_115_);
v___x_116_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_86_, v_size_115_, v_index_114_, v_val_105_, v_val_106_);
lean_dec(v_index_114_);
v___y_89_ = v___x_116_;
goto v___jp_88_;
}
case 1:
{
lean_object* v_index_117_; 
v_index_117_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_index_117_);
lean_dec_ref_known(v___x_113_, 1);
v_i_108_ = v_index_117_;
goto v___jp_107_;
}
default: 
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_86_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_index_120_; 
v_index_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_index_120_);
lean_dec_ref_known(v___x_119_, 1);
v_i_108_ = v_index_120_;
goto v___jp_107_;
}
else
{
lean_dec(v_val_106_);
lean_dec(v_val_105_);
v___y_89_ = v_acc_86_;
goto v___jp_88_;
}
}
}
v___jp_107_:
{
lean_object* v_size_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_size_109_ = lean_ctor_get(v_acc_86_, 0);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_size_109_, v___x_110_);
v___x_112_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_86_, v___x_111_, v_i_108_, v_val_105_, v_val_106_);
lean_dec(v_i_108_);
v___y_89_ = v___x_112_;
goto v___jp_88_;
}
}
}
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_i_87_, v___x_90_);
lean_dec(v_i_87_);
v_acc_86_ = v___y_89_;
v_i_87_ = v___x_91_;
goto _start;
}
v___jp_93_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_i_87_, v___x_94_);
lean_dec(v_i_87_);
v_i_87_ = v___x_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_121_, lean_object* v_acc_122_, lean_object* v_i_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg(v_b_121_, v_acc_122_, v_i_123_);
lean_dec_ref(v_b_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg(lean_object* v_init_125_, lean_object* v_b_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg(v_b_126_, v_init_125_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg___boxed(lean_object* v_init_129_, lean_object* v_b_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg(v_init_129_, v_b_130_);
lean_dec_ref(v_b_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(lean_object* v_m_132_){
_start:
{
lean_object* v_keyArray_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_cellCount_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_target_140_; lean_object* v___x_141_; 
v_keyArray_133_ = lean_ctor_get(v_m_132_, 1);
v___x_134_ = lean_array_get_size(v_keyArray_133_);
v___x_135_ = lean_unsigned_to_nat(2u);
v_cellCount_136_ = lean_nat_mul(v___x_134_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_136_);
v___x_138_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_136_);
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_136_);
v_target_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_140_, 0, v___x_137_);
lean_ctor_set(v_target_140_, 1, v___x_138_);
lean_ctor_set(v_target_140_, 2, v___x_139_);
v___x_141_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg(v_target_140_, v_m_132_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg___boxed(lean_object* v_m_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(v_m_142_);
lean_dec_ref(v_m_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(lean_object* v_m_144_, lean_object* v_query_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_m_144_, v_query_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_index_147_; lean_object* v_key_148_; lean_object* v_value_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_index_147_ = lean_ctor_get(v___x_146_, 0);
v_key_148_ = lean_ctor_get(v___x_146_, 1);
v_value_149_ = lean_ctor_get(v___x_146_, 2);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_146_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_value_149_);
lean_inc(v_key_148_);
lean_inc(v_index_147_);
lean_dec(v___x_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_index_147_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_key_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_value_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v___x_146_);
v___x_157_ = lean_box(1);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg___boxed(lean_object* v_m_158_, lean_object* v_query_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_m_158_, v_query_159_);
lean_dec_ref(v_query_159_);
lean_dec_ref(v_m_158_);
return v_res_160_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object* v_m_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_m_161_, v_a_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
uint8_t v___x_164_; 
lean_dec_ref_known(v___x_163_, 3);
v___x_164_ = 1;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object* v_m_166_, lean_object* v_a_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_166_, v_a_167_);
lean_dec_ref(v_a_167_);
lean_dec_ref(v_m_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object* v_visitConst_170_, lean_object* v_e_171_, lean_object* v_acc_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_d_175_; lean_object* v_b_176_; lean_object* v___y_177_; lean_object* v_visited_182_; lean_object* v_visitedConsts_183_; lean_object* v___y_185_; uint8_t v___x_218_; 
v_visited_182_ = lean_ctor_get(v_a_173_, 0);
v_visitedConsts_183_ = lean_ctor_get(v_a_173_, 1);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_visited_182_, v_e_171_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___y_221_; lean_object* v_i_222_; lean_object* v___y_228_; lean_object* v___y_238_; lean_object* v_i_239_; lean_object* v___x_254_; 
lean_inc_ref(v_visitedConsts_183_);
lean_inc_ref(v_visited_182_);
lean_dec_ref(v_a_173_);
v___x_219_ = lean_box(0);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_visited_182_, v_e_171_);
switch(lean_obj_tag(v___x_254_))
{
case 0:
{
lean_dec_ref_known(v___x_254_, 3);
v___y_185_ = v_visited_182_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_255_; lean_object* v_size_256_; lean_object* v_keyArray_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_index_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_index_255_);
lean_dec_ref_known(v___x_254_, 1);
v_size_256_ = lean_ctor_get(v_visited_182_, 0);
v_keyArray_257_ = lean_ctor_get(v_visited_182_, 1);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_size_256_, v___x_258_);
v___x_260_ = lean_array_get_size(v_keyArray_257_);
v___x_261_ = lean_nat_dec_lt(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_dec(v___x_259_);
lean_dec(v_index_255_);
goto v___jp_244_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_262_ = lean_unsigned_to_nat(4u);
v___x_263_ = lean_nat_mul(v___x_259_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = lean_nat_mul(v___x_260_, v___x_264_);
v___x_266_ = lean_nat_dec_le(v___x_263_, v___x_265_);
lean_dec(v___x_265_);
lean_dec(v___x_263_);
if (v___x_266_ == 0)
{
lean_dec(v___x_259_);
lean_dec(v_index_255_);
goto v___jp_244_;
}
else
{
lean_object* v___x_267_; 
lean_inc_ref(v_e_171_);
v___x_267_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visited_182_, v___x_259_, v_index_255_, v_e_171_, v___x_219_);
lean_dec(v_index_255_);
v___y_185_ = v___x_267_;
goto v___jp_184_;
}
}
}
default: 
{
lean_object* v_size_268_; lean_object* v_keyArray_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_size_268_ = lean_ctor_get(v_visited_182_, 0);
v_keyArray_269_ = lean_ctor_get(v_visited_182_, 1);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_size_268_, v___x_270_);
v___x_272_ = lean_array_get_size(v_keyArray_269_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v___x_271_);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(v_visited_182_);
lean_dec_ref(v_visited_182_);
v___y_228_ = v___x_274_;
goto v___jp_227_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_275_ = lean_unsigned_to_nat(4u);
v___x_276_ = lean_nat_mul(v___x_271_, v___x_275_);
lean_dec(v___x_271_);
v___x_277_ = lean_unsigned_to_nat(3u);
v___x_278_ = lean_nat_mul(v___x_272_, v___x_277_);
v___x_279_ = lean_nat_dec_le(v___x_276_, v___x_278_);
lean_dec(v___x_278_);
lean_dec(v___x_276_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(v_visited_182_);
lean_dec_ref(v_visited_182_);
v___y_228_ = v___x_280_;
goto v___jp_227_;
}
else
{
v___y_228_ = v_visited_182_;
goto v___jp_227_;
}
}
}
}
v___jp_220_:
{
lean_object* v_size_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_size_223_ = lean_ctor_get(v___y_221_, 0);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_size_223_, v___x_224_);
lean_inc_ref(v_e_171_);
v___x_226_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_221_, v___x_225_, v_i_222_, v_e_171_, v___x_219_);
lean_dec(v_i_222_);
v___y_185_ = v___x_226_;
goto v___jp_184_;
}
v___jp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v___y_228_, v_e_171_);
switch(lean_obj_tag(v___x_229_))
{
case 0:
{
lean_object* v_index_230_; lean_object* v_size_231_; lean_object* v___x_232_; 
v_index_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_index_230_);
lean_dec_ref_known(v___x_229_, 3);
v_size_231_ = lean_ctor_get(v___y_228_, 0);
lean_inc(v_size_231_);
lean_inc_ref(v_e_171_);
v___x_232_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_228_, v_size_231_, v_index_230_, v_e_171_, v___x_219_);
lean_dec(v_index_230_);
v___y_185_ = v___x_232_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_233_; 
v_index_233_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_index_233_);
lean_dec_ref_known(v___x_229_, 1);
v___y_221_ = v___y_228_;
v_i_222_ = v_index_233_;
goto v___jp_220_;
}
default: 
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_228_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_index_236_; 
v_index_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_index_236_);
lean_dec_ref_known(v___x_235_, 1);
v___y_221_ = v___y_228_;
v_i_222_ = v_index_236_;
goto v___jp_220_;
}
else
{
v___y_185_ = v___y_228_;
goto v___jp_184_;
}
}
}
}
v___jp_237_:
{
lean_object* v_size_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_size_240_ = lean_ctor_get(v___y_238_, 0);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_size_240_, v___x_241_);
lean_inc_ref(v_e_171_);
v___x_243_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_238_, v___x_242_, v_i_239_, v_e_171_, v___x_219_);
lean_dec(v_i_239_);
v___y_185_ = v___x_243_;
goto v___jp_184_;
}
v___jp_244_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(v_visited_182_);
lean_dec_ref(v_visited_182_);
v___x_246_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v___x_245_, v_e_171_);
switch(lean_obj_tag(v___x_246_))
{
case 0:
{
lean_object* v_index_247_; lean_object* v_size_248_; lean_object* v___x_249_; 
v_index_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_index_247_);
lean_dec_ref_known(v___x_246_, 3);
v_size_248_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_size_248_);
lean_inc_ref(v_e_171_);
v___x_249_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_245_, v_size_248_, v_index_247_, v_e_171_, v___x_219_);
lean_dec(v_index_247_);
v___y_185_ = v___x_249_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_250_; 
v_index_250_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_index_250_);
lean_dec_ref_known(v___x_246_, 1);
v___y_238_ = v___x_245_;
v_i_239_ = v_index_250_;
goto v___jp_237_;
}
default: 
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_245_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_index_253_; 
v_index_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_index_253_);
lean_dec_ref_known(v___x_252_, 1);
v___y_238_ = v___x_245_;
v_i_239_ = v_index_253_;
goto v___jp_237_;
}
else
{
v___y_185_ = v___x_245_;
goto v___jp_184_;
}
}
}
}
}
else
{
lean_object* v___x_281_; 
lean_dec_ref(v_e_171_);
lean_dec_ref(v_visitConst_170_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_acc_172_);
lean_ctor_set(v___x_281_, 1, v_a_173_);
return v___x_281_;
}
v___jp_174_:
{
lean_object* v___x_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; 
lean_inc_ref(v_visitConst_170_);
v___x_178_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_170_, v_d_175_, v_acc_172_, v___y_177_);
v_fst_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v___x_178_);
v_e_171_ = v_b_176_;
v_acc_172_ = v_fst_179_;
v_a_173_ = v_snd_180_;
goto _start;
}
v___jp_184_:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___y_185_);
lean_ctor_set(v___x_186_, 1, v_visitedConsts_183_);
switch(lean_obj_tag(v_e_171_))
{
case 7:
{
lean_object* v_binderType_187_; lean_object* v_body_188_; 
v_binderType_187_ = lean_ctor_get(v_e_171_, 1);
lean_inc_ref(v_binderType_187_);
v_body_188_ = lean_ctor_get(v_e_171_, 2);
lean_inc_ref(v_body_188_);
lean_dec_ref_known(v_e_171_, 3);
v_d_175_ = v_binderType_187_;
v_b_176_ = v_body_188_;
v___y_177_ = v___x_186_;
goto v___jp_174_;
}
case 6:
{
lean_object* v_binderType_189_; lean_object* v_body_190_; 
v_binderType_189_ = lean_ctor_get(v_e_171_, 1);
lean_inc_ref(v_binderType_189_);
v_body_190_ = lean_ctor_get(v_e_171_, 2);
lean_inc_ref(v_body_190_);
lean_dec_ref_known(v_e_171_, 3);
v_d_175_ = v_binderType_189_;
v_b_176_ = v_body_190_;
v___y_177_ = v___x_186_;
goto v___jp_174_;
}
case 10:
{
lean_object* v_expr_191_; 
v_expr_191_ = lean_ctor_get(v_e_171_, 1);
lean_inc_ref(v_expr_191_);
lean_dec_ref_known(v_e_171_, 2);
v_e_171_ = v_expr_191_;
v_a_173_ = v___x_186_;
goto _start;
}
case 8:
{
lean_object* v_type_193_; lean_object* v_value_194_; lean_object* v_body_195_; lean_object* v___x_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; lean_object* v_fst_200_; lean_object* v_snd_201_; 
v_type_193_ = lean_ctor_get(v_e_171_, 1);
lean_inc_ref(v_type_193_);
v_value_194_ = lean_ctor_get(v_e_171_, 2);
lean_inc_ref(v_value_194_);
v_body_195_ = lean_ctor_get(v_e_171_, 3);
lean_inc_ref(v_body_195_);
lean_dec_ref_known(v_e_171_, 4);
lean_inc_ref_n(v_visitConst_170_, 2);
v___x_196_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_170_, v_type_193_, v_acc_172_, v___x_186_);
v_fst_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v___x_196_, 1);
lean_inc(v_snd_198_);
lean_dec_ref(v___x_196_);
v___x_199_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_170_, v_value_194_, v_fst_197_, v_snd_198_);
v_fst_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_fst_200_);
v_snd_201_ = lean_ctor_get(v___x_199_, 1);
lean_inc(v_snd_201_);
lean_dec_ref(v___x_199_);
v_e_171_ = v_body_195_;
v_acc_172_ = v_fst_200_;
v_a_173_ = v_snd_201_;
goto _start;
}
case 5:
{
lean_object* v_fn_203_; lean_object* v_arg_204_; lean_object* v___x_205_; lean_object* v_fst_206_; lean_object* v_snd_207_; 
v_fn_203_ = lean_ctor_get(v_e_171_, 0);
lean_inc_ref(v_fn_203_);
v_arg_204_ = lean_ctor_get(v_e_171_, 1);
lean_inc_ref(v_arg_204_);
lean_dec_ref_known(v_e_171_, 2);
lean_inc_ref(v_visitConst_170_);
v___x_205_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_170_, v_fn_203_, v_acc_172_, v___x_186_);
v_fst_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_fst_206_);
v_snd_207_ = lean_ctor_get(v___x_205_, 1);
lean_inc(v_snd_207_);
lean_dec_ref(v___x_205_);
v_e_171_ = v_arg_204_;
v_acc_172_ = v_fst_206_;
v_a_173_ = v_snd_207_;
goto _start;
}
case 11:
{
lean_object* v_typeName_209_; lean_object* v_struct_210_; lean_object* v___x_211_; lean_object* v_fst_212_; lean_object* v_snd_213_; 
v_typeName_209_ = lean_ctor_get(v_e_171_, 0);
lean_inc(v_typeName_209_);
v_struct_210_ = lean_ctor_get(v_e_171_, 2);
lean_inc_ref(v_struct_210_);
lean_dec_ref_known(v_e_171_, 3);
lean_inc_ref(v_visitConst_170_);
v___x_211_ = lean_apply_3(v_visitConst_170_, v_typeName_209_, v_acc_172_, v___x_186_);
v_fst_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_snd_213_);
lean_dec_ref(v___x_211_);
v_e_171_ = v_struct_210_;
v_acc_172_ = v_fst_212_;
v_a_173_ = v_snd_213_;
goto _start;
}
case 4:
{
lean_object* v_declName_215_; lean_object* v___x_216_; 
v_declName_215_ = lean_ctor_get(v_e_171_, 0);
lean_inc(v_declName_215_);
lean_dec_ref_known(v_e_171_, 2);
v___x_216_ = lean_apply_3(v_visitConst_170_, v_declName_215_, v_acc_172_, v___x_186_);
return v___x_216_;
}
default: 
{
lean_object* v___x_217_; 
lean_dec_ref(v_e_171_);
lean_dec_ref(v_visitConst_170_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_acc_172_);
lean_ctor_set(v___x_217_, 1, v___x_186_);
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_object* v_00_u03b1_282_, lean_object* v_visitConst_283_, lean_object* v_e_284_, lean_object* v_acc_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_283_, v_e_284_, v_acc_285_, v_a_286_);
return v___x_287_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object* v_00_u03b2_288_, lean_object* v_m_289_, lean_object* v_a_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_289_, v_a_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object* v_00_u03b2_292_, lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(v_00_u03b2_292_, v_m_293_, v_a_294_);
lean_dec_ref(v_a_294_);
lean_dec_ref(v_m_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_query_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_m_298_, v_query_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_query_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(v_00_u03b2_301_, v_m_302_, v_query_303_);
lean_dec_ref(v_query_303_);
lean_dec_ref(v_m_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2(lean_object* v_00_u03b2_305_, lean_object* v_m_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___redArg(v_m_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2___boxed(lean_object* v_00_u03b2_308_, lean_object* v_m_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2(v_00_u03b2_308_, v_m_309_);
lean_dec_ref(v_m_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(lean_object* v_00_u03b2_311_, lean_object* v_m_312_, lean_object* v_query_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_m_312_, v_query_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_315_, lean_object* v_m_316_, lean_object* v_query_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(v_00_u03b2_315_, v_m_316_, v_query_317_);
lean_dec_ref(v_query_317_);
lean_dec_ref(v_m_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_query_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_m_320_, v_query_321_, v_x_322_, v_x_323_, v_x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_query_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(v_00_u03b2_327_, v_m_328_, v_query_329_, v_x_330_, v_x_331_, v_x_332_, v_x_333_);
lean_dec_ref(v_query_329_);
lean_dec_ref(v_m_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4(lean_object* v_00_u03b2_335_, lean_object* v_init_336_, lean_object* v_b_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___redArg(v_init_336_, v_b_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4___boxed(lean_object* v_00_u03b2_339_, lean_object* v_init_340_, lean_object* v_b_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4(v_00_u03b2_339_, v_init_340_, v_b_341_);
lean_dec_ref(v_b_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_343_, lean_object* v_b_344_, lean_object* v_acc_345_, lean_object* v_i_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___redArg(v_b_344_, v_acc_345_, v_i_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_348_, lean_object* v_b_349_, lean_object* v_acc_350_, lean_object* v_i_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__2_spec__4_spec__5(v_00_u03b2_348_, v_b_349_, v_acc_350_, v_i_351_);
lean_dec_ref(v_b_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0(lean_object* v_f_353_, lean_object* v_c_354_, lean_object* v_acc_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_visited_357_; lean_object* v_visitedConsts_358_; uint8_t v___x_359_; 
v_visited_357_ = lean_ctor_get(v___y_356_, 0);
v_visitedConsts_358_ = lean_ctor_get(v___y_356_, 1);
v___x_359_ = l_Lean_NameHashSet_contains(v_visitedConsts_358_, v_c_354_);
if (v___x_359_ == 0)
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_369_; 
lean_inc_ref(v_visitedConsts_358_);
lean_inc_ref(v_visited_357_);
v_isSharedCheck_369_ = !lean_is_exclusive(v___y_356_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_370_ = lean_ctor_get(v___y_356_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v___y_356_, 0);
lean_dec(v_unused_371_);
v___x_361_ = v___y_356_;
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
else
{
lean_dec(v___y_356_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
lean_inc(v_c_354_);
v___x_363_ = l_Lean_NameHashSet_insert(v_visitedConsts_358_, v_c_354_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_visited_357_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_368_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_apply_2(v_f_353_, v_c_354_, v_acc_355_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
return v___x_367_;
}
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v_c_354_);
lean_dec(v_f_353_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_acc_355_);
lean_ctor_set(v___x_372_, 1, v___y_356_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object* v_f_373_, lean_object* v_e_374_, lean_object* v_acc_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_visitConst_377_; lean_object* v___x_378_; 
v_visitConst_377_ = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0), 4, 1);
lean_closure_set(v_visitConst_377_, 0, v_f_373_);
v___x_378_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_377_, v_e_374_, v_acc_375_, v_a_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* v_00_u03b1_379_, lean_object* v_f_380_, lean_object* v_e_381_, lean_object* v_acc_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_380_, v_e_381_, v_acc_382_, v_a_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(64u);
v___x_386_ = l_Lean_mkPtrSet___redArg(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_387_; lean_object* v___x_388_; 
v_cellCount_387_ = lean_unsigned_to_nat(16u);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_389_; lean_object* v___x_390_; 
v_cellCount_389_ = lean_unsigned_to_nat(16u);
v___x_390_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2);
v___x_392_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_396_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object* v_e_398_, lean_object* v_init_399_, lean_object* v_f_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_fst_403_; 
v___x_401_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4);
v___x_402_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_400_, v_e_398_, v_init_399_, v___x_401_);
v_fst_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_fst_403_);
lean_dec_ref(v___x_402_);
return v_fst_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* v_00_u03b1_404_, lean_object* v_e_405_, lean_object* v_init_406_, lean_object* v_f_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_fst_410_; 
v___x_408_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4);
v___x_409_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_407_, v_e_405_, v_init_406_, v___x_408_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
lean_dec_ref(v___x_409_);
return v_fst_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object* v_c_411_, lean_object* v_cs_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_array_push(v_cs_412_, v_c_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* v_e_417_){
_start:
{
lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_fst_422_; 
v___f_418_ = ((lean_object*)(l_Lean_Expr_getUsedConstants___closed__0));
v___x_419_ = ((lean_object*)(l_Lean_Expr_getUsedConstants___closed__1));
v___x_420_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4);
v___x_421_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v___f_418_, v_e_417_, v___x_419_, v___x_420_);
v_fst_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_fst_422_);
lean_dec_ref(v___x_421_);
return v_fst_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object* v_c_423_, lean_object* v_cs_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_NameSet_insert(v_cs_424_, v_c_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* v_e_427_){
_start:
{
lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_fst_432_; 
v___f_428_ = ((lean_object*)(l_Lean_Expr_getUsedConstantsAsSet___closed__0));
v___x_429_ = l_Lean_NameSet_empty;
v___x_430_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__4);
v___x_431_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v___f_428_, v_e_427_, v___x_429_, v___x_430_);
v_fst_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_fst_432_);
lean_dec_ref(v___x_431_);
return v_fst_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* v_c_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_ConstantInfo_type(v_c_433_);
v___x_435_ = l_Lean_Expr_getUsedConstantsAsSet(v___x_434_);
v___x_436_ = 1;
lean_inc_ref(v_c_433_);
v___x_437_ = l_Lean_ConstantInfo_value_x3f(v_c_433_, v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
switch(lean_obj_tag(v_c_433_))
{
case 5:
{
lean_object* v_val_438_; lean_object* v_ctors_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_val_438_ = lean_ctor_get(v_c_433_, 0);
lean_inc_ref(v_val_438_);
lean_dec_ref_known(v_c_433_, 1);
v_ctors_439_ = lean_ctor_get(v_val_438_, 4);
lean_inc(v_ctors_439_);
lean_dec_ref(v_val_438_);
v___x_440_ = l_Lean_NameSet_ofList(v_ctors_439_);
lean_dec(v_ctors_439_);
v___x_441_ = l_Lean_NameSet_append(v___x_435_, v___x_440_);
return v___x_441_;
}
case 6:
{
lean_object* v_val_442_; lean_object* v_toConstantVal_443_; lean_object* v_name_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_val_442_ = lean_ctor_get(v_c_433_, 0);
lean_inc_ref(v_val_442_);
lean_dec_ref_known(v_c_433_, 1);
v_toConstantVal_443_ = lean_ctor_get(v_val_442_, 0);
lean_inc_ref(v_toConstantVal_443_);
lean_dec_ref(v_val_442_);
v_name_444_ = lean_ctor_get(v_toConstantVal_443_, 0);
lean_inc(v_name_444_);
lean_dec_ref(v_toConstantVal_443_);
v___x_445_ = l_Lean_NameSet_empty;
v___x_446_ = l_Lean_NameSet_insert(v___x_445_, v_name_444_);
v___x_447_ = l_Lean_NameSet_append(v___x_435_, v___x_446_);
return v___x_447_;
}
case 7:
{
lean_object* v_val_448_; lean_object* v_all_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_val_448_ = lean_ctor_get(v_c_433_, 0);
lean_inc_ref(v_val_448_);
lean_dec_ref_known(v_c_433_, 1);
v_all_449_ = lean_ctor_get(v_val_448_, 1);
lean_inc(v_all_449_);
lean_dec_ref(v_val_448_);
v___x_450_ = l_Lean_NameSet_ofList(v_all_449_);
lean_dec(v_all_449_);
v___x_451_ = l_Lean_NameSet_append(v___x_435_, v___x_450_);
return v___x_451_;
}
default: 
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v_c_433_);
v___x_452_ = l_Lean_NameSet_empty;
v___x_453_ = l_Lean_NameSet_append(v___x_435_, v___x_452_);
return v___x_453_;
}
}
}
else
{
lean_object* v_val_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref(v_c_433_);
v_val_454_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_454_);
lean_dec_ref_known(v___x_437_, 1);
v___x_455_ = l_Lean_Expr_getUsedConstantsAsSet(v_val_454_);
v___x_456_ = l_Lean_NameSet_append(v___x_435_, v___x_455_);
return v___x_456_;
}
}
}
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_FoldConsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_FoldConsts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
lean_object* initialize_Lean_Declaration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_FoldConsts(builtin);
}
#ifdef __cplusplus
}
#endif
