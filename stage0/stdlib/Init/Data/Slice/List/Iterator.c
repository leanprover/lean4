// Lean compiler output
// Module: Init.Data.Slice.List.Iterator
// Imports: public import Init.Data.Slice.List.Basic public import Init.Data.Iterators.Producers.List public import Init.Data.Iterators.Combinators.Take import all Init.Data.Range.Polymorphic.Basic public import Init.Data.Slice.Operations public import Init.Data.ToString.Extra
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_toSlice___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_ListSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ListSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ListSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_ListSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_instSliceSizeListSliceData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceSizeListSliceData___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceSizeListSliceData___redArg___closed__0 = (const lean_object*)&l_instSliceSizeListSliceData___redArg___closed__0_value;
static const lean_closure_object l_instSliceSizeListSliceData___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceSizeListSliceData___redArg___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_instSliceSizeListSliceData___redArg___closed__0_value)} };
static const lean_object* l_instSliceSizeListSliceData___redArg___closed__1 = (const lean_object*)&l_instSliceSizeListSliceData___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg();
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___boxed(lean_object*);
static lean_once_cell_t l_instSliceSizeListSliceData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instSliceSizeListSliceData___closed__0;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_instAppendListSlice___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_instAppendListSlice___redArg___lam__2___closed__0 = (const lean_object*)&l_List_instAppendListSlice___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instAppendListSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instAppendListSlice___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instAppendListSlice___redArg___closed__0 = (const lean_object*)&l_List_instAppendListSlice___redArg___closed__0_value;
static const lean_closure_object l_List_instAppendListSlice___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instAppendListSlice___redArg___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_List_instAppendListSlice___redArg___closed__0_value),((lean_object*)&l_List_instAppendListSlice___redArg___closed__0_value)} };
static const lean_object* l_List_instAppendListSlice___redArg___closed__1 = (const lean_object*)&l_List_instAppendListSlice___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg();
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___boxed(lean_object*);
static lean_once_cell_t l_List_instAppendListSlice___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_instAppendListSlice___closed__0;
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object*);
static const lean_string_object l_List_ListSlice_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ".toSlice 0 "};
static const lean_object* l_List_ListSlice_repr___redArg___closed__0 = (const lean_object*)&l_List_ListSlice_repr___redArg___closed__0_value;
static const lean_ctor_object l_List_ListSlice_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_ListSlice_repr___redArg___closed__0_value)}};
static const lean_object* l_List_ListSlice_repr___redArg___closed__1 = (const lean_object*)&l_List_ListSlice_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object*, lean_object*);
static const lean_string_object l_List_instToStringListSlice___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_List_instToStringListSlice___redArg___lam__1___closed__0 = (const lean_object*)&l_List_instToStringListSlice___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v_stop_2_; 
v_stop_2_ = lean_ctor_get(v_x_1_, 1);
if (lean_obj_tag(v_stop_2_) == 0)
{
lean_object* v_list_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_list_3_ = lean_ctor_get(v_x_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_11_ == 0)
{
lean_object* v_unused_12_; 
v_unused_12_ = lean_ctor_get(v_x_1_, 1);
lean_dec(v_unused_12_);
v___x_5_ = v_x_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_list_3_);
lean_dec(v_x_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(0u);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v_list_3_);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_list_3_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_list_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
lean_inc_ref(v_stop_2_);
v_list_13_ = lean_ctor_get(v_x_1_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v_x_1_, 1);
lean_dec(v_unused_24_);
v___x_15_ = v_x_1_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_list_13_);
lean_dec(v_x_1_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_val_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v_val_17_ = lean_ctor_get(v_stop_2_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_stop_2_, 1);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_val_17_, v___x_18_);
lean_dec(v_val_17_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v_list_13_);
lean_ctor_set(v___x_15_, 0, v___x_19_);
v___x_21_ = v___x_15_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_list_13_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_ListSlice_instToIterator___redArg___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_ListSlice_instToIterator___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object* v_00_u03b1_30_){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = ((lean_object*)(l_ListSlice_instToIterator___redArg___closed__0));
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__0(lean_object* v_it_32_, lean_object* v_acc_33_, lean_object* v_hP_34_, lean_object* v_recur_35_){
_start:
{
lean_object* v_countdown_36_; lean_object* v_inner_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_50_; 
v_countdown_36_ = lean_ctor_get(v_it_32_, 0);
v_inner_37_ = lean_ctor_get(v_it_32_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_it_32_);
if (v_isSharedCheck_50_ == 0)
{
v___x_39_ = v_it_32_;
v_isShared_40_ = v_isSharedCheck_50_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_inner_37_);
lean_inc(v_countdown_36_);
lean_dec(v_it_32_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_50_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_dec_eq(v_countdown_36_, v___x_41_);
if (v___x_42_ == 0)
{
if (lean_obj_tag(v_inner_37_) == 0)
{
lean_del_object(v___x_39_);
lean_dec(v_countdown_36_);
lean_dec_ref(v_recur_35_);
lean_inc(v_acc_33_);
return v_acc_33_;
}
else
{
lean_object* v_tail_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v_tail_43_ = lean_ctor_get(v_inner_37_, 1);
lean_inc(v_tail_43_);
lean_dec_ref_known(v_inner_37_, 2);
v___x_44_ = lean_nat_sub(v_countdown_36_, v___x_41_);
lean_dec(v_countdown_36_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 1, v_tail_43_);
lean_ctor_set(v___x_39_, 0, v___x_44_);
v___x_46_ = v___x_39_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_tail_43_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_nat_add(v_acc_33_, v___x_41_);
v___x_48_ = lean_apply_4(v_recur_35_, v___x_46_, v___x_47_, lean_box(0), lean_box(0));
return v___x_48_;
}
}
}
else
{
lean_del_object(v___x_39_);
lean_dec(v_inner_37_);
lean_dec(v_countdown_36_);
lean_dec_ref(v_recur_35_);
lean_inc(v_acc_33_);
return v_acc_33_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__0___boxed(lean_object* v_it_51_, lean_object* v_acc_52_, lean_object* v_hP_53_, lean_object* v_recur_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_instSliceSizeListSliceData___redArg___lam__0(v_it_51_, v_acc_52_, v_hP_53_, v_recur_54_);
lean_dec(v_acc_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__1(lean_object* v___f_56_, lean_object* v_s_57_){
_start:
{
lean_object* v___y_59_; lean_object* v_stop_62_; 
v_stop_62_ = lean_ctor_get(v_s_57_, 1);
if (lean_obj_tag(v_stop_62_) == 0)
{
lean_object* v_list_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_71_; 
v_list_63_ = lean_ctor_get(v_s_57_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v_s_57_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_s_57_, 1);
lean_dec(v_unused_72_);
v___x_65_ = v_s_57_;
v_isShared_66_ = v_isSharedCheck_71_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_list_63_);
lean_dec(v_s_57_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_71_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(0u);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_list_63_);
lean_ctor_set(v___x_65_, 0, v___x_67_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_list_63_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
v___y_59_ = v___x_69_;
goto v___jp_58_;
}
}
}
else
{
lean_object* v_list_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_83_; 
lean_inc_ref(v_stop_62_);
v_list_73_ = lean_ctor_get(v_s_57_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_s_57_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v_s_57_, 1);
lean_dec(v_unused_84_);
v___x_75_ = v_s_57_;
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_list_73_);
lean_dec(v_s_57_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v_val_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v_val_77_ = lean_ctor_get(v_stop_62_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v_stop_62_, 1);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_val_77_, v___x_78_);
lean_dec(v_val_77_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_list_73_);
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_81_ = v___x_75_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_list_73_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v___y_59_ = v___x_81_;
goto v___jp_58_;
}
}
}
v___jp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_56_, v___y_59_, v___x_60_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg(){
_start:
{
lean_object* v___f_89_; 
v___f_89_ = ((lean_object*)(l_instSliceSizeListSliceData___redArg___closed__1));
return v___f_89_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_instSliceSizeListSliceData___redArg();
return v_res_91_;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_instSliceSizeListSliceData___redArg();
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* v_00_u03b1_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_instSliceSizeListSliceData___closed__0, &l_instSliceSizeListSliceData___closed__0_once, _init_l_instSliceSizeListSliceData___closed__0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object* v_toPure_95_, lean_object* v_____do__lift_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_2(v_toPure_95_, lean_box(0), v_____do__lift_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object* v_toPure_98_, lean_object* v_recur_99_, lean_object* v___x_100_, lean_object* v_____do__lift_101_){
_start:
{
if (lean_obj_tag(v_____do__lift_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; 
lean_dec_ref(v___x_100_);
lean_dec(v_recur_99_);
v_a_102_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v_____do__lift_101_, 1);
v___x_103_ = lean_apply_2(v_toPure_98_, lean_box(0), v_a_102_);
return v___x_103_;
}
else
{
lean_object* v_a_104_; lean_object* v___x_105_; 
lean_dec(v_toPure_98_);
v_a_104_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v_____do__lift_101_, 1);
v___x_105_ = lean_apply_4(v_recur_99_, v___x_100_, v_a_104_, lean_box(0), lean_box(0));
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object* v_toPure_106_, lean_object* v_f_107_, lean_object* v_toBind_108_, lean_object* v___f_109_, lean_object* v_it_110_, lean_object* v_acc_111_, lean_object* v_hP_112_, lean_object* v_recur_113_){
_start:
{
lean_object* v_countdown_114_; lean_object* v_inner_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_133_; 
v_countdown_114_ = lean_ctor_get(v_it_110_, 0);
v_inner_115_ = lean_ctor_get(v_it_110_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_it_110_);
if (v_isSharedCheck_133_ == 0)
{
v___x_117_ = v_it_110_;
v_isShared_118_ = v_isSharedCheck_133_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_inner_115_);
lean_inc(v_countdown_114_);
lean_dec(v_it_110_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_133_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_dec_eq(v_countdown_114_, v___x_119_);
if (v___x_120_ == 0)
{
if (lean_obj_tag(v_inner_115_) == 0)
{
lean_object* v___x_121_; 
lean_del_object(v___x_117_);
lean_dec(v_countdown_114_);
lean_dec(v_recur_113_);
lean_dec(v___f_109_);
lean_dec(v_toBind_108_);
lean_dec(v_f_107_);
v___x_121_ = lean_apply_2(v_toPure_106_, lean_box(0), v_acc_111_);
return v___x_121_;
}
else
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v_head_122_ = lean_ctor_get(v_inner_115_, 0);
lean_inc(v_head_122_);
v_tail_123_ = lean_ctor_get(v_inner_115_, 1);
lean_inc(v_tail_123_);
lean_dec_ref_known(v_inner_115_, 2);
v___x_124_ = lean_nat_sub(v_countdown_114_, v___x_119_);
lean_dec(v_countdown_114_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_tail_123_);
lean_ctor_set(v___x_117_, 0, v___x_124_);
v___x_126_ = v___x_117_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_tail_123_);
v___x_126_ = v_reuseFailAlloc_131_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___f_127_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_127_, 0, v_toPure_106_);
lean_closure_set(v___f_127_, 1, v_recur_113_);
lean_closure_set(v___f_127_, 2, v___x_126_);
v___x_128_ = lean_apply_2(v_f_107_, v_head_122_, v_acc_111_);
lean_inc(v_toBind_108_);
v___x_129_ = lean_apply_4(v_toBind_108_, lean_box(0), lean_box(0), v___x_128_, v___f_109_);
v___x_130_ = lean_apply_4(v_toBind_108_, lean_box(0), lean_box(0), v___x_129_, v___f_127_);
return v___x_130_;
}
}
}
else
{
lean_object* v___x_132_; 
lean_del_object(v___x_117_);
lean_dec(v_inner_115_);
lean_dec(v_countdown_114_);
lean_dec(v_recur_113_);
lean_dec(v___f_109_);
lean_dec(v_toBind_108_);
lean_dec(v_f_107_);
v___x_132_ = lean_apply_2(v_toPure_106_, lean_box(0), v_acc_111_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object* v_inst_134_, lean_object* v_00_u03b2_135_, lean_object* v_xs_136_, lean_object* v_init_137_, lean_object* v_f_138_){
_start:
{
lean_object* v___y_140_; lean_object* v_stop_147_; 
v_stop_147_ = lean_ctor_get(v_xs_136_, 1);
if (lean_obj_tag(v_stop_147_) == 0)
{
lean_object* v_list_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
v_list_148_ = lean_ctor_get(v_xs_136_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_xs_136_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_xs_136_, 1);
lean_dec(v_unused_157_);
v___x_150_ = v_xs_136_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_list_148_);
lean_dec(v_xs_136_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_unsigned_to_nat(0u);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_list_148_);
lean_ctor_set(v___x_150_, 0, v___x_152_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_list_148_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
v___y_140_ = v___x_154_;
goto v___jp_139_;
}
}
}
else
{
lean_object* v_list_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
lean_inc_ref(v_stop_147_);
v_list_158_ = lean_ctor_get(v_xs_136_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_xs_136_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v_xs_136_, 1);
lean_dec(v_unused_169_);
v___x_160_ = v_xs_136_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_list_158_);
lean_dec(v_xs_136_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_val_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v_val_162_ = lean_ctor_get(v_stop_147_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v_stop_147_, 1);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_val_162_, v___x_163_);
lean_dec(v_val_162_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_list_158_);
lean_ctor_set(v___x_160_, 0, v___x_164_);
v___x_166_ = v___x_160_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_list_158_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v___y_140_ = v___x_166_;
goto v___jp_139_;
}
}
}
v___jp_139_:
{
lean_object* v_toApplicative_141_; lean_object* v_toBind_142_; lean_object* v_toPure_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_134_, 0);
lean_inc_ref(v_toApplicative_141_);
v_toBind_142_ = lean_ctor_get(v_inst_134_, 1);
lean_inc(v_toBind_142_);
lean_dec_ref(v_inst_134_);
v_toPure_143_ = lean_ctor_get(v_toApplicative_141_, 1);
lean_inc_n(v_toPure_143_, 2);
lean_dec_ref(v_toApplicative_141_);
v___f_144_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_144_, 0, v_toPure_143_);
v___f_145_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_145_, 0, v_toPure_143_);
lean_closure_set(v___f_145_, 1, v_f_138_);
lean_closure_set(v___f_145_, 2, v_toBind_142_);
lean_closure_set(v___f_145_, 3, v___f_144_);
v___x_146_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_145_, v___y_140_, v_init_137_, lean_box(0));
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object* v_inst_170_){
_start:
{
lean_object* v___f_171_; 
v___f_171_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_171_, 0, v_inst_170_);
return v___f_171_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object* v_00_u03b1_172_, lean_object* v_m_173_, lean_object* v_inst_174_){
_start:
{
lean_object* v___f_175_; 
v___f_175_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_175_, 0, v_inst_174_);
return v___f_175_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___lam__0(lean_object* v_it_176_, lean_object* v_acc_177_, lean_object* v_recur_178_){
_start:
{
lean_object* v_countdown_179_; lean_object* v_inner_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_194_; 
v_countdown_179_ = lean_ctor_get(v_it_176_, 0);
v_inner_180_ = lean_ctor_get(v_it_176_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_it_176_);
if (v_isSharedCheck_194_ == 0)
{
v___x_182_ = v_it_176_;
v_isShared_183_ = v_isSharedCheck_194_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_inner_180_);
lean_inc(v_countdown_179_);
lean_dec(v_it_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_194_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_dec_eq(v_countdown_179_, v___x_184_);
if (v___x_185_ == 0)
{
if (lean_obj_tag(v_inner_180_) == 0)
{
lean_del_object(v___x_182_);
lean_dec(v_countdown_179_);
lean_dec_ref(v_recur_178_);
return v_acc_177_;
}
else
{
lean_object* v_head_186_; lean_object* v_tail_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v_head_186_ = lean_ctor_get(v_inner_180_, 0);
lean_inc(v_head_186_);
v_tail_187_ = lean_ctor_get(v_inner_180_, 1);
lean_inc(v_tail_187_);
lean_dec_ref_known(v_inner_180_, 2);
v___x_188_ = lean_nat_sub(v_countdown_179_, v___x_184_);
lean_dec(v_countdown_179_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_tail_187_);
lean_ctor_set(v___x_182_, 0, v___x_188_);
v___x_190_ = v___x_182_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_tail_187_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_array_push(v_acc_177_, v_head_186_);
v___x_192_ = lean_apply_3(v_recur_178_, v___x_190_, v___x_191_, lean_box(0));
return v___x_192_;
}
}
}
else
{
lean_del_object(v___x_182_);
lean_dec(v_inner_180_);
lean_dec(v_countdown_179_);
lean_dec_ref(v_recur_178_);
return v_acc_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___lam__2(lean_object* v___f_197_, lean_object* v___f_198_, lean_object* v_x_199_, lean_object* v_y_200_){
_start:
{
lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_212_; lean_object* v_stop_232_; 
v_stop_232_ = lean_ctor_get(v_x_199_, 1);
if (lean_obj_tag(v_stop_232_) == 0)
{
lean_object* v_list_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_list_233_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_x_199_, 1);
lean_dec(v_unused_242_);
v___x_235_ = v_x_199_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_list_233_);
lean_dec(v_x_199_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(0u);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_list_233_);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_list_233_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v___y_212_ = v___x_239_;
goto v___jp_211_;
}
}
}
else
{
lean_object* v_list_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_253_; 
lean_inc_ref(v_stop_232_);
v_list_243_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v_x_199_, 1);
lean_dec(v_unused_254_);
v___x_245_ = v_x_199_;
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_list_243_);
lean_dec(v_x_199_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_val_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_val_247_ = lean_ctor_get(v_stop_232_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v_stop_232_, 1);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_add(v_val_247_, v___x_248_);
lean_dec(v_val_247_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_list_243_);
lean_ctor_set(v___x_245_, 0, v___x_249_);
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_list_243_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v___y_212_ = v___x_251_;
goto v___jp_211_;
}
}
}
v___jp_201_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_197_, v___y_205_, v___y_202_);
v___x_207_ = lean_array_to_list(v___x_206_);
v_a_208_ = l_List_appendTR___redArg(v___y_204_, v___x_207_);
v___x_209_ = l_List_lengthTR___redArg(v_a_208_);
v___x_210_ = l_List_toSlice___redArg(v_a_208_, v___y_203_, v___x_209_);
lean_dec(v___x_209_);
lean_dec(v_a_208_);
return v___x_210_;
}
v___jp_211_:
{
lean_object* v_list_213_; lean_object* v_stop_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_231_; 
v_list_213_ = lean_ctor_get(v_y_200_, 0);
v_stop_214_ = lean_ctor_get(v_y_200_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_y_200_);
if (v_isSharedCheck_231_ == 0)
{
v___x_216_ = v_y_200_;
v_isShared_217_ = v_isSharedCheck_231_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_stop_214_);
lean_inc(v_list_213_);
lean_dec(v_y_200_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_231_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = ((lean_object*)(l_List_instAppendListSlice___redArg___lam__2___closed__0));
v___x_220_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_198_, v___y_212_, v___x_219_);
v___x_221_ = lean_array_to_list(v___x_220_);
if (lean_obj_tag(v_stop_214_) == 0)
{
lean_object* v___x_223_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v_list_213_);
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_223_ = v___x_216_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_list_213_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
v___y_202_ = v___x_219_;
v___y_203_ = v___x_218_;
v___y_204_ = v___x_221_;
v___y_205_ = v___x_223_;
goto v___jp_201_;
}
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v_val_225_ = lean_ctor_get(v_stop_214_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_stop_214_, 1);
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_val_225_, v___x_226_);
lean_dec(v_val_225_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v_list_213_);
lean_ctor_set(v___x_216_, 0, v___x_227_);
v___x_229_ = v___x_216_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_list_213_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v___y_202_ = v___x_219_;
v___y_203_ = v___x_218_;
v___y_204_ = v___x_221_;
v___y_205_ = v___x_229_;
goto v___jp_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg(){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = ((lean_object*)(l_List_instAppendListSlice___redArg___closed__1));
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___boxed(lean_object* v___dummy_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_List_instAppendListSlice___redArg();
return v_res_261_;
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__0(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_List_instAppendListSlice___redArg();
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* v_00_u03b1_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_List_instAppendListSlice___closed__0, &l_List_instAppendListSlice___closed__0_once, _init_l_List_instAppendListSlice___closed__0);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object* v_inst_268_, lean_object* v_s_269_){
_start:
{
lean_object* v_list_270_; lean_object* v_stop_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_296_; 
v_list_270_ = lean_ctor_get(v_s_269_, 0);
v_stop_271_ = lean_ctor_get(v_s_269_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_s_269_);
if (v_isSharedCheck_296_ == 0)
{
v___x_273_ = v_s_269_;
v_isShared_274_ = v_isSharedCheck_296_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_stop_271_);
lean_inc(v_list_270_);
lean_dec(v_s_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_296_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___f_275_; lean_object* v___y_277_; 
v___f_275_ = ((lean_object*)(l_List_instAppendListSlice___redArg___closed__0));
if (lean_obj_tag(v_stop_271_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_list_270_);
v___y_277_ = v___x_291_;
goto v___jp_276_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_val_292_ = lean_ctor_get(v_stop_271_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_stop_271_, 1);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_val_292_, v___x_293_);
lean_dec(v_val_292_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_list_270_);
v___y_277_ = v___x_295_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_278_ = ((lean_object*)(l_List_instAppendListSlice___redArg___lam__2___closed__0));
v___x_279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_275_, v___y_277_, v___x_278_);
v___x_280_ = lean_array_to_list(v___x_279_);
lean_inc(v___x_280_);
v___x_281_ = l_List_repr___redArg(v_inst_268_, v___x_280_);
v___x_282_ = ((lean_object*)(l_List_ListSlice_repr___redArg___closed__1));
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 5);
lean_ctor_set(v___x_273_, 1, v___x_282_);
lean_ctor_set(v___x_273_, 0, v___x_281_);
v___x_284_ = v___x_273_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_289_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = l_List_lengthTR___redArg(v___x_280_);
lean_dec(v___x_280_);
v___x_286_ = l_Nat_reprFast(v___x_285_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_284_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_s_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_List_ListSlice_repr___redArg(v_inst_298_, v_s_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object* v_inst_301_, lean_object* v_s_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_List_ListSlice_repr___redArg(v_inst_301_, v_s_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object* v_inst_305_, lean_object* v_s_306_, lean_object* v_x_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_List_instReprListSlice___redArg___lam__0(v_inst_305_, v_s_306_, v_x_307_);
lean_dec(v_x_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object* v_inst_309_){
_start:
{
lean_object* v___f_310_; 
v___f_310_ = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_310_, 0, v_inst_309_);
return v___f_310_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object* v_00_u03b1_311_, lean_object* v_inst_312_){
_start:
{
lean_object* v___f_313_; 
v___f_313_ = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_313_, 0, v_inst_312_);
return v___f_313_;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object* v___f_315_, lean_object* v_inst_316_, lean_object* v_s_317_){
_start:
{
lean_object* v___y_319_; lean_object* v_stop_326_; 
v_stop_326_ = lean_ctor_get(v_s_317_, 1);
if (lean_obj_tag(v_stop_326_) == 0)
{
lean_object* v_list_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_list_327_ = lean_ctor_get(v_s_317_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_s_317_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_s_317_, 1);
lean_dec(v_unused_336_);
v___x_329_ = v_s_317_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_list_327_);
lean_dec(v_s_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_unsigned_to_nat(0u);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_list_327_);
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_list_327_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
v___y_319_ = v___x_333_;
goto v___jp_318_;
}
}
}
else
{
lean_object* v_list_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_347_; 
lean_inc_ref(v_stop_326_);
v_list_337_ = lean_ctor_get(v_s_317_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_s_317_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_s_317_, 1);
lean_dec(v_unused_348_);
v___x_339_ = v_s_317_;
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_list_337_);
lean_dec(v_s_317_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_val_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v_val_341_ = lean_ctor_get(v_stop_326_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v_stop_326_, 1);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_val_341_, v___x_342_);
lean_dec(v_val_341_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_list_337_);
lean_ctor_set(v___x_339_, 0, v___x_343_);
v___x_345_ = v___x_339_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_list_337_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
v___y_319_ = v___x_345_;
goto v___jp_318_;
}
}
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_320_ = ((lean_object*)(l_List_instAppendListSlice___redArg___lam__2___closed__0));
v___x_321_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_315_, v___y_319_, v___x_320_);
v___x_322_ = ((lean_object*)(l_List_instToStringListSlice___redArg___lam__1___closed__0));
v___x_323_ = lean_array_to_list(v___x_321_);
v___x_324_ = l_List_toString___redArg(v_inst_316_, v___x_323_);
v___x_325_ = lean_string_append(v___x_322_, v___x_324_);
lean_dec_ref(v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* v_inst_349_){
_start:
{
lean_object* v___f_350_; lean_object* v___f_351_; 
v___f_350_ = ((lean_object*)(l_List_instAppendListSlice___redArg___closed__0));
v___f_351_ = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__1), 3, 2);
lean_closure_set(v___f_351_, 0, v___f_350_);
lean_closure_set(v___f_351_, 1, v_inst_349_);
return v___f_351_;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object* v_00_u03b1_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_List_instToStringListSlice___redArg(v_inst_353_);
return v___x_354_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Producers_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Producers_List(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_List_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_List_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
