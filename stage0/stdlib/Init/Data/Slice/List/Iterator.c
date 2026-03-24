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
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_ListSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ListSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ListSlice_instToIterator___closed__0 = (const lean_object*)&l_ListSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_instSliceSizeListSliceData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceSizeListSliceData___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceSizeListSliceData___closed__0 = (const lean_object*)&l_instSliceSizeListSliceData___closed__0_value;
static const lean_closure_object l_instSliceSizeListSliceData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceSizeListSliceData___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_instSliceSizeListSliceData___closed__0_value)} };
static const lean_object* l_instSliceSizeListSliceData___closed__1 = (const lean_object*)&l_instSliceSizeListSliceData___closed__1_value;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_instAppendListSlice___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_instAppendListSlice___lam__2___closed__0 = (const lean_object*)&l_List_instAppendListSlice___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instAppendListSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instAppendListSlice___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instAppendListSlice___closed__0 = (const lean_object*)&l_List_instAppendListSlice___closed__0_value;
static lean_once_cell_t l_List_instAppendListSlice___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_instAppendListSlice___closed__1;
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
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object* v_x_1_){
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
lean_dec_ref(v_stop_2_);
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
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object* v_00_u03b1_26_){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_ListSlice_instToIterator___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object* v_it_28_, lean_object* v_acc_29_, lean_object* v_hP_30_, lean_object* v_recur_31_){
_start:
{
lean_object* v_countdown_32_; lean_object* v_inner_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_46_; 
v_countdown_32_ = lean_ctor_get(v_it_28_, 0);
v_inner_33_ = lean_ctor_get(v_it_28_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_it_28_);
if (v_isSharedCheck_46_ == 0)
{
v___x_35_ = v_it_28_;
v_isShared_36_ = v_isSharedCheck_46_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_inner_33_);
lean_inc(v_countdown_32_);
lean_dec(v_it_28_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_46_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_dec_eq(v_countdown_32_, v___x_37_);
if (v___x_38_ == 0)
{
if (lean_obj_tag(v_inner_33_) == 0)
{
lean_del_object(v___x_35_);
lean_dec(v_countdown_32_);
lean_dec_ref(v_recur_31_);
lean_inc(v_acc_29_);
return v_acc_29_;
}
else
{
lean_object* v_tail_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v_tail_39_ = lean_ctor_get(v_inner_33_, 1);
lean_inc(v_tail_39_);
lean_dec_ref(v_inner_33_);
v___x_40_ = lean_nat_sub(v_countdown_32_, v___x_37_);
lean_dec(v_countdown_32_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v_tail_39_);
lean_ctor_set(v___x_35_, 0, v___x_40_);
v___x_42_ = v___x_35_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_tail_39_);
v___x_42_ = v_reuseFailAlloc_45_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_nat_add(v_acc_29_, v___x_37_);
v___x_44_ = lean_apply_4(v_recur_31_, v___x_42_, v___x_43_, lean_box(0), lean_box(0));
return v___x_44_;
}
}
}
else
{
lean_del_object(v___x_35_);
lean_dec(v_inner_33_);
lean_dec(v_countdown_32_);
lean_dec_ref(v_recur_31_);
lean_inc(v_acc_29_);
return v_acc_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0___boxed(lean_object* v_it_47_, lean_object* v_acc_48_, lean_object* v_hP_49_, lean_object* v_recur_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_instSliceSizeListSliceData___lam__0(v_it_47_, v_acc_48_, v_hP_49_, v_recur_50_);
lean_dec(v_acc_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object* v___f_52_, lean_object* v_s_53_){
_start:
{
lean_object* v___y_55_; lean_object* v_stop_58_; 
v_stop_58_ = lean_ctor_get(v_s_53_, 1);
if (lean_obj_tag(v_stop_58_) == 0)
{
lean_object* v_list_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
v_list_59_ = lean_ctor_get(v_s_53_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_s_53_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v_s_53_, 1);
lean_dec(v_unused_68_);
v___x_61_ = v_s_53_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_list_59_);
lean_dec(v_s_53_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(0u);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_list_59_);
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_list_59_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
v___y_55_ = v___x_65_;
goto v___jp_54_;
}
}
}
else
{
lean_object* v_list_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
lean_inc_ref(v_stop_58_);
v_list_69_ = lean_ctor_get(v_s_53_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_s_53_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_s_53_, 1);
lean_dec(v_unused_80_);
v___x_71_ = v_s_53_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_list_69_);
lean_dec(v_s_53_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_val_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v_val_73_ = lean_ctor_get(v_stop_58_, 0);
lean_inc(v_val_73_);
lean_dec_ref(v_stop_58_);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_val_73_, v___x_74_);
lean_dec(v_val_73_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v_list_69_);
lean_ctor_set(v___x_71_, 0, v___x_75_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_list_69_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v___y_55_ = v___x_77_;
goto v___jp_54_;
}
}
}
v___jp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_52_, v___y_55_, v___x_56_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* v_00_u03b1_84_){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = ((lean_object*)(l_instSliceSizeListSliceData___closed__1));
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object* v_toPure_86_, lean_object* v_____do__lift_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_apply_2(v_toPure_86_, lean_box(0), v_____do__lift_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object* v_toPure_89_, lean_object* v_recur_90_, lean_object* v___x_91_, lean_object* v_____do__lift_92_){
_start:
{
if (lean_obj_tag(v_____do__lift_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec_ref(v___x_91_);
lean_dec(v_recur_90_);
v_a_93_ = lean_ctor_get(v_____do__lift_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref(v_____do__lift_92_);
v___x_94_ = lean_apply_2(v_toPure_89_, lean_box(0), v_a_93_);
return v___x_94_;
}
else
{
lean_object* v_a_95_; lean_object* v___x_96_; 
lean_dec(v_toPure_89_);
v_a_95_ = lean_ctor_get(v_____do__lift_92_, 0);
lean_inc(v_a_95_);
lean_dec_ref(v_____do__lift_92_);
v___x_96_ = lean_apply_4(v_recur_90_, v___x_91_, v_a_95_, lean_box(0), lean_box(0));
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object* v_toPure_97_, lean_object* v_f_98_, lean_object* v_toBind_99_, lean_object* v___f_100_, lean_object* v_it_101_, lean_object* v_acc_102_, lean_object* v_hP_103_, lean_object* v_recur_104_){
_start:
{
lean_object* v_countdown_105_; lean_object* v_inner_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_124_; 
v_countdown_105_ = lean_ctor_get(v_it_101_, 0);
v_inner_106_ = lean_ctor_get(v_it_101_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_it_101_);
if (v_isSharedCheck_124_ == 0)
{
v___x_108_ = v_it_101_;
v_isShared_109_ = v_isSharedCheck_124_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_inner_106_);
lean_inc(v_countdown_105_);
lean_dec(v_it_101_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_124_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_dec_eq(v_countdown_105_, v___x_110_);
if (v___x_111_ == 0)
{
if (lean_obj_tag(v_inner_106_) == 0)
{
lean_object* v___x_112_; 
lean_del_object(v___x_108_);
lean_dec(v_countdown_105_);
lean_dec(v_recur_104_);
lean_dec(v___f_100_);
lean_dec(v_toBind_99_);
lean_dec(v_f_98_);
v___x_112_ = lean_apply_2(v_toPure_97_, lean_box(0), v_acc_102_);
return v___x_112_;
}
else
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v_head_113_ = lean_ctor_get(v_inner_106_, 0);
lean_inc(v_head_113_);
v_tail_114_ = lean_ctor_get(v_inner_106_, 1);
lean_inc(v_tail_114_);
lean_dec_ref(v_inner_106_);
v___x_115_ = lean_nat_sub(v_countdown_105_, v___x_110_);
lean_dec(v_countdown_105_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_tail_114_);
lean_ctor_set(v___x_108_, 0, v___x_115_);
v___x_117_ = v___x_108_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_tail_114_);
v___x_117_ = v_reuseFailAlloc_122_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___f_118_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_118_, 0, v_toPure_97_);
lean_closure_set(v___f_118_, 1, v_recur_104_);
lean_closure_set(v___f_118_, 2, v___x_117_);
v___x_119_ = lean_apply_2(v_f_98_, v_head_113_, v_acc_102_);
lean_inc(v_toBind_99_);
v___x_120_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v___x_119_, v___f_100_);
v___x_121_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v___x_120_, v___f_118_);
return v___x_121_;
}
}
}
else
{
lean_object* v___x_123_; 
lean_del_object(v___x_108_);
lean_dec(v_inner_106_);
lean_dec(v_countdown_105_);
lean_dec(v_recur_104_);
lean_dec(v___f_100_);
lean_dec(v_toBind_99_);
lean_dec(v_f_98_);
v___x_123_ = lean_apply_2(v_toPure_97_, lean_box(0), v_acc_102_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object* v_inst_125_, lean_object* v_00_u03b2_126_, lean_object* v_xs_127_, lean_object* v_init_128_, lean_object* v_f_129_){
_start:
{
lean_object* v___y_131_; lean_object* v_stop_138_; 
v_stop_138_ = lean_ctor_get(v_xs_127_, 1);
if (lean_obj_tag(v_stop_138_) == 0)
{
lean_object* v_list_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
v_list_139_ = lean_ctor_get(v_xs_127_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_xs_127_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v_xs_127_, 1);
lean_dec(v_unused_148_);
v___x_141_ = v_xs_127_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_list_139_);
lean_dec(v_xs_127_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(0u);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v_list_139_);
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_list_139_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
v___y_131_ = v___x_145_;
goto v___jp_130_;
}
}
}
else
{
lean_object* v_list_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_159_; 
lean_inc_ref(v_stop_138_);
v_list_149_ = lean_ctor_get(v_xs_127_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_xs_127_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_xs_127_, 1);
lean_dec(v_unused_160_);
v___x_151_ = v_xs_127_;
v_isShared_152_ = v_isSharedCheck_159_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_list_149_);
lean_dec(v_xs_127_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_159_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_val_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v_val_153_ = lean_ctor_get(v_stop_138_, 0);
lean_inc(v_val_153_);
lean_dec_ref(v_stop_138_);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_val_153_, v___x_154_);
lean_dec(v_val_153_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_list_149_);
lean_ctor_set(v___x_151_, 0, v___x_155_);
v___x_157_ = v___x_151_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_list_149_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v___y_131_ = v___x_157_;
goto v___jp_130_;
}
}
}
v___jp_130_:
{
lean_object* v_toApplicative_132_; lean_object* v_toBind_133_; lean_object* v_toPure_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___x_137_; 
v_toApplicative_132_ = lean_ctor_get(v_inst_125_, 0);
lean_inc_ref(v_toApplicative_132_);
v_toBind_133_ = lean_ctor_get(v_inst_125_, 1);
lean_inc(v_toBind_133_);
lean_dec_ref(v_inst_125_);
v_toPure_134_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_134_);
lean_dec_ref(v_toApplicative_132_);
lean_inc(v_toPure_134_);
v___f_135_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_135_, 0, v_toPure_134_);
v___f_136_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_136_, 0, v_toPure_134_);
lean_closure_set(v___f_136_, 1, v_f_129_);
lean_closure_set(v___f_136_, 2, v_toBind_133_);
lean_closure_set(v___f_136_, 3, v___f_135_);
v___x_137_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_136_, v___y_131_, v_init_128_, lean_box(0));
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object* v_inst_161_){
_start:
{
lean_object* v___f_162_; 
v___f_162_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_162_, 0, v_inst_161_);
return v___f_162_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object* v_00_u03b1_163_, lean_object* v_m_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_166_, 0, v_inst_165_);
return v___f_166_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object* v_it_167_, lean_object* v_acc_168_, lean_object* v_recur_169_){
_start:
{
lean_object* v_countdown_170_; lean_object* v_inner_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_185_; 
v_countdown_170_ = lean_ctor_get(v_it_167_, 0);
v_inner_171_ = lean_ctor_get(v_it_167_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_it_167_);
if (v_isSharedCheck_185_ == 0)
{
v___x_173_ = v_it_167_;
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_inner_171_);
lean_inc(v_countdown_170_);
lean_dec(v_it_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_dec_eq(v_countdown_170_, v___x_175_);
if (v___x_176_ == 0)
{
if (lean_obj_tag(v_inner_171_) == 0)
{
lean_del_object(v___x_173_);
lean_dec(v_countdown_170_);
lean_dec_ref(v_recur_169_);
return v_acc_168_;
}
else
{
lean_object* v_head_177_; lean_object* v_tail_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v_head_177_ = lean_ctor_get(v_inner_171_, 0);
lean_inc(v_head_177_);
v_tail_178_ = lean_ctor_get(v_inner_171_, 1);
lean_inc(v_tail_178_);
lean_dec_ref(v_inner_171_);
v___x_179_ = lean_nat_sub(v_countdown_170_, v___x_175_);
lean_dec(v_countdown_170_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v_tail_178_);
lean_ctor_set(v___x_173_, 0, v___x_179_);
v___x_181_ = v___x_173_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_tail_178_);
v___x_181_ = v_reuseFailAlloc_184_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_array_push(v_acc_168_, v_head_177_);
v___x_183_ = lean_apply_3(v_recur_169_, v___x_181_, v___x_182_, lean_box(0));
return v___x_183_;
}
}
}
else
{
lean_del_object(v___x_173_);
lean_dec(v_inner_171_);
lean_dec(v_countdown_170_);
lean_dec_ref(v_recur_169_);
return v_acc_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__2(lean_object* v___f_188_, lean_object* v___f_189_, lean_object* v_x_190_, lean_object* v_y_191_){
_start:
{
lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_203_; lean_object* v_stop_223_; 
v_stop_223_ = lean_ctor_get(v_x_190_, 1);
if (lean_obj_tag(v_stop_223_) == 0)
{
lean_object* v_list_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_list_224_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v_x_190_, 1);
lean_dec(v_unused_233_);
v___x_226_ = v_x_190_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_list_224_);
lean_dec(v_x_190_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(0u);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v_list_224_);
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_list_224_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
v___y_203_ = v___x_230_;
goto v___jp_202_;
}
}
}
else
{
lean_object* v_list_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
lean_inc_ref(v_stop_223_);
v_list_234_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_x_190_, 1);
lean_dec(v_unused_245_);
v___x_236_ = v_x_190_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_list_234_);
lean_dec(v_x_190_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_val_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v_val_238_ = lean_ctor_get(v_stop_223_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v_stop_223_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_val_238_, v___x_239_);
lean_dec(v_val_238_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_list_234_);
lean_ctor_set(v___x_236_, 0, v___x_240_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_list_234_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v___y_203_ = v___x_242_;
goto v___jp_202_;
}
}
}
v___jp_192_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_188_, v___y_196_, v___y_193_);
v___x_198_ = lean_array_to_list(v___x_197_);
v_a_199_ = l_List_appendTR___redArg(v___y_194_, v___x_198_);
v___x_200_ = l_List_lengthTR___redArg(v_a_199_);
v___x_201_ = l_List_toSlice___redArg(v_a_199_, v___y_195_, v___x_200_);
lean_dec(v___x_200_);
lean_dec(v_a_199_);
return v___x_201_;
}
v___jp_202_:
{
lean_object* v_list_204_; lean_object* v_stop_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_222_; 
v_list_204_ = lean_ctor_get(v_y_191_, 0);
v_stop_205_ = lean_ctor_get(v_y_191_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_y_191_);
if (v_isSharedCheck_222_ == 0)
{
v___x_207_ = v_y_191_;
v_isShared_208_ = v_isSharedCheck_222_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_stop_205_);
lean_inc(v_list_204_);
lean_dec(v_y_191_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_222_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = ((lean_object*)(l_List_instAppendListSlice___lam__2___closed__0));
v___x_211_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_189_, v___y_203_, v___x_210_);
v___x_212_ = lean_array_to_list(v___x_211_);
if (lean_obj_tag(v_stop_205_) == 0)
{
lean_object* v___x_214_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_list_204_);
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_214_ = v___x_207_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_list_204_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
v___y_193_ = v___x_210_;
v___y_194_ = v___x_212_;
v___y_195_ = v___x_209_;
v___y_196_ = v___x_214_;
goto v___jp_192_;
}
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v_val_216_ = lean_ctor_get(v_stop_205_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v_stop_205_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_val_216_, v___x_217_);
lean_dec(v_val_216_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_list_204_);
lean_ctor_set(v___x_207_, 0, v___x_218_);
v___x_220_ = v___x_207_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_list_204_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
v___y_193_ = v___x_210_;
v___y_194_ = v___x_212_;
v___y_195_ = v___x_209_;
v___y_196_ = v___x_220_;
goto v___jp_192_;
}
}
}
}
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__1(void){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; 
v___f_247_ = ((lean_object*)(l_List_instAppendListSlice___closed__0));
v___f_248_ = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__2), 4, 2);
lean_closure_set(v___f_248_, 0, v___f_247_);
lean_closure_set(v___f_248_, 1, v___f_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* v_00_u03b1_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_obj_once(&l_List_instAppendListSlice___closed__1, &l_List_instAppendListSlice___closed__1_once, _init_l_List_instAppendListSlice___closed__1);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object* v_inst_254_, lean_object* v_s_255_){
_start:
{
lean_object* v_list_256_; lean_object* v_stop_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_282_; 
v_list_256_ = lean_ctor_get(v_s_255_, 0);
v_stop_257_ = lean_ctor_get(v_s_255_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_s_255_);
if (v_isSharedCheck_282_ == 0)
{
v___x_259_ = v_s_255_;
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_stop_257_);
lean_inc(v_list_256_);
lean_dec(v_s_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___f_261_; lean_object* v___y_263_; 
v___f_261_ = ((lean_object*)(l_List_instAppendListSlice___closed__0));
if (lean_obj_tag(v_stop_257_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_list_256_);
v___y_263_ = v___x_277_;
goto v___jp_262_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_val_278_ = lean_ctor_get(v_stop_257_, 0);
lean_inc(v_val_278_);
lean_dec_ref(v_stop_257_);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_val_278_, v___x_279_);
lean_dec(v_val_278_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_list_256_);
v___y_263_ = v___x_281_;
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_264_ = ((lean_object*)(l_List_instAppendListSlice___lam__2___closed__0));
v___x_265_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_261_, v___y_263_, v___x_264_);
v___x_266_ = lean_array_to_list(v___x_265_);
lean_inc(v___x_266_);
v___x_267_ = l_List_repr___redArg(v_inst_254_, v___x_266_);
v___x_268_ = ((lean_object*)(l_List_ListSlice_repr___redArg___closed__1));
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 5);
lean_ctor_set(v___x_259_, 1, v___x_268_);
lean_ctor_set(v___x_259_, 0, v___x_267_);
v___x_270_ = v___x_259_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_275_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = l_List_lengthTR___redArg(v___x_266_);
lean_dec(v___x_266_);
v___x_272_ = l_Nat_reprFast(v___x_271_);
v___x_273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_270_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_s_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_List_ListSlice_repr___redArg(v_inst_284_, v_s_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object* v_inst_287_, lean_object* v_s_288_, lean_object* v_x_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_List_ListSlice_repr___redArg(v_inst_287_, v_s_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object* v_inst_291_, lean_object* v_s_292_, lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_List_instReprListSlice___redArg___lam__0(v_inst_291_, v_s_292_, v_x_293_);
lean_dec(v_x_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object* v_inst_295_){
_start:
{
lean_object* v___f_296_; 
v___f_296_ = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_296_, 0, v_inst_295_);
return v___f_296_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_){
_start:
{
lean_object* v___f_299_; 
v___f_299_ = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_299_, 0, v_inst_298_);
return v___f_299_;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object* v___f_301_, lean_object* v_inst_302_, lean_object* v_s_303_){
_start:
{
lean_object* v___y_305_; lean_object* v_stop_312_; 
v_stop_312_ = lean_ctor_get(v_s_303_, 1);
if (lean_obj_tag(v_stop_312_) == 0)
{
lean_object* v_list_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_list_313_ = lean_ctor_get(v_s_303_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_s_303_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_s_303_, 1);
lean_dec(v_unused_322_);
v___x_315_ = v_s_303_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_list_313_);
lean_dec(v_s_303_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(0u);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v_list_313_);
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_list_313_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v___y_305_ = v___x_319_;
goto v___jp_304_;
}
}
}
else
{
lean_object* v_list_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_333_; 
lean_inc_ref(v_stop_312_);
v_list_323_ = lean_ctor_get(v_s_303_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_s_303_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_s_303_, 1);
lean_dec(v_unused_334_);
v___x_325_ = v_s_303_;
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_list_323_);
lean_dec(v_s_303_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_val_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v_val_327_ = lean_ctor_get(v_stop_312_, 0);
lean_inc(v_val_327_);
lean_dec_ref(v_stop_312_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_val_327_, v___x_328_);
lean_dec(v_val_327_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_list_323_);
lean_ctor_set(v___x_325_, 0, v___x_329_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_list_323_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
v___y_305_ = v___x_331_;
goto v___jp_304_;
}
}
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l_List_instAppendListSlice___lam__2___closed__0));
v___x_307_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_301_, v___y_305_, v___x_306_);
v___x_308_ = ((lean_object*)(l_List_instToStringListSlice___redArg___lam__1___closed__0));
v___x_309_ = lean_array_to_list(v___x_307_);
v___x_310_ = l_List_toString___redArg(v_inst_302_, v___x_309_);
v___x_311_ = lean_string_append(v___x_308_, v___x_310_);
lean_dec_ref(v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* v_inst_335_){
_start:
{
lean_object* v___f_336_; lean_object* v___f_337_; 
v___f_336_ = ((lean_object*)(l_List_instAppendListSlice___closed__0));
v___f_337_ = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__1), 3, 2);
lean_closure_set(v___f_337_, 0, v___f_336_);
lean_closure_set(v___f_337_, 1, v_inst_335_);
return v___f_337_;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object* v_00_u03b1_338_, lean_object* v_inst_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_List_instToStringListSlice___redArg(v_inst_339_);
return v___x_340_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Producers_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
