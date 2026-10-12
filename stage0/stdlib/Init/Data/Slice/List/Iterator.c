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
lean_object* l_ListSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_ListSlice_instToIterator___redArg___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT void l_ListSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_28_;
v_res_28_ = l_ListSlice_instToIterator___redArg();
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___redArg___boxed(lean_object* v___dummy_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_ListSlice_instToIterator___redArg();
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object* v_00_u03b1_31_){
_start:
{
lean_object* v___f_32_; 
v___f_32_ = ((lean_object*)(l_ListSlice_instToIterator___redArg___closed__0));
return v___f_32_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__0(lean_object* v_it_33_, lean_object* v_acc_34_, lean_object* v_hP_35_, lean_object* v_recur_36_){
_start:
{
lean_object* v_countdown_37_; lean_object* v_inner_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_51_; 
v_countdown_37_ = lean_ctor_get(v_it_33_, 0);
v_inner_38_ = lean_ctor_get(v_it_33_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_it_33_);
if (v_isSharedCheck_51_ == 0)
{
v___x_40_ = v_it_33_;
v_isShared_41_ = v_isSharedCheck_51_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_inner_38_);
lean_inc(v_countdown_37_);
lean_dec(v_it_33_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_51_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_dec_eq(v_countdown_37_, v___x_42_);
if (v___x_43_ == 0)
{
if (lean_obj_tag(v_inner_38_) == 0)
{
lean_del_object(v___x_40_);
lean_dec(v_countdown_37_);
lean_dec_ref(v_recur_36_);
lean_inc(v_acc_34_);
return v_acc_34_;
}
else
{
lean_object* v_tail_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v_tail_44_ = lean_ctor_get(v_inner_38_, 1);
lean_inc(v_tail_44_);
lean_dec_ref_known(v_inner_38_, 2);
v___x_45_ = lean_nat_sub(v_countdown_37_, v___x_42_);
lean_dec(v_countdown_37_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v_tail_44_);
lean_ctor_set(v___x_40_, 0, v___x_45_);
v___x_47_ = v___x_40_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_tail_44_);
v___x_47_ = v_reuseFailAlloc_50_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_nat_add(v_acc_34_, v___x_42_);
v___x_49_ = lean_apply_4(v_recur_36_, v___x_47_, v___x_48_, lean_box(0), lean_box(0));
return v___x_49_;
}
}
}
else
{
lean_del_object(v___x_40_);
lean_dec(v_inner_38_);
lean_dec(v_countdown_37_);
lean_dec_ref(v_recur_36_);
lean_inc(v_acc_34_);
return v_acc_34_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__0___boxed(lean_object* v_it_52_, lean_object* v_acc_53_, lean_object* v_hP_54_, lean_object* v_recur_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_instSliceSizeListSliceData___redArg___lam__0(v_it_52_, v_acc_53_, v_hP_54_, v_recur_55_);
lean_dec(v_acc_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___lam__1(lean_object* v___f_57_, lean_object* v_s_58_){
_start:
{
lean_object* v___y_60_; lean_object* v_stop_63_; 
v_stop_63_ = lean_ctor_get(v_s_58_, 1);
if (lean_obj_tag(v_stop_63_) == 0)
{
lean_object* v_list_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_72_; 
v_list_64_ = lean_ctor_get(v_s_58_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v_s_58_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v_s_58_, 1);
lean_dec(v_unused_73_);
v___x_66_ = v_s_58_;
v_isShared_67_ = v_isSharedCheck_72_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_list_64_);
lean_dec(v_s_58_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_72_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(0u);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v_list_64_);
lean_ctor_set(v___x_66_, 0, v___x_68_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_list_64_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v___y_60_ = v___x_70_;
goto v___jp_59_;
}
}
}
else
{
lean_object* v_list_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_84_; 
lean_inc_ref(v_stop_63_);
v_list_74_ = lean_ctor_get(v_s_58_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_s_58_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v_s_58_, 1);
lean_dec(v_unused_85_);
v___x_76_ = v_s_58_;
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_list_74_);
lean_dec(v_s_58_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v_val_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v_val_78_ = lean_ctor_get(v_stop_63_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_stop_63_, 1);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_val_78_, v___x_79_);
lean_dec(v_val_78_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v_list_74_);
lean_ctor_set(v___x_76_, 0, v___x_80_);
v___x_82_ = v___x_76_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_list_74_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v___y_60_ = v___x_82_;
goto v___jp_59_;
}
}
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_57_, v___y_60_, v___x_61_, lean_box(0));
return v___x_62_;
}
}
}
lean_object* l_instSliceSizeListSliceData___redArg(){
_start:
{
lean_object* v___f_90_; 
v___f_90_ = ((lean_object*)(l_instSliceSizeListSliceData___redArg___closed__1));
return v___f_90_;
}
}
LEAN_EXPORT void l_instSliceSizeListSliceData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_91_;
v_res_91_ = l_instSliceSizeListSliceData___redArg();
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___redArg___boxed(lean_object* v___dummy_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_instSliceSizeListSliceData___redArg();
return v_res_93_;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__0(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_instSliceSizeListSliceData___redArg();
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* v_00_u03b1_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_instSliceSizeListSliceData___closed__0, &l_instSliceSizeListSliceData___closed__0_once, _init_l_instSliceSizeListSliceData___closed__0);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object* v_toPure_97_, lean_object* v_____do__lift_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_2(v_toPure_97_, lean_box(0), v_____do__lift_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object* v_toPure_100_, lean_object* v_recur_101_, lean_object* v___x_102_, lean_object* v_____do__lift_103_){
_start:
{
if (lean_obj_tag(v_____do__lift_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; 
lean_dec_ref(v___x_102_);
lean_dec(v_recur_101_);
v_a_104_ = lean_ctor_get(v_____do__lift_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v_____do__lift_103_, 1);
v___x_105_ = lean_apply_2(v_toPure_100_, lean_box(0), v_a_104_);
return v___x_105_;
}
else
{
lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_toPure_100_);
v_a_106_ = lean_ctor_get(v_____do__lift_103_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v_____do__lift_103_, 1);
v___x_107_ = lean_apply_4(v_recur_101_, v___x_102_, v_a_106_, lean_box(0), lean_box(0));
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object* v_toPure_108_, lean_object* v_f_109_, lean_object* v_toBind_110_, lean_object* v___f_111_, lean_object* v_it_112_, lean_object* v_acc_113_, lean_object* v_hP_114_, lean_object* v_recur_115_){
_start:
{
lean_object* v_countdown_116_; lean_object* v_inner_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_135_; 
v_countdown_116_ = lean_ctor_get(v_it_112_, 0);
v_inner_117_ = lean_ctor_get(v_it_112_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_it_112_);
if (v_isSharedCheck_135_ == 0)
{
v___x_119_ = v_it_112_;
v_isShared_120_ = v_isSharedCheck_135_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_inner_117_);
lean_inc(v_countdown_116_);
lean_dec(v_it_112_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_135_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_dec_eq(v_countdown_116_, v___x_121_);
if (v___x_122_ == 0)
{
if (lean_obj_tag(v_inner_117_) == 0)
{
lean_object* v___x_123_; 
lean_del_object(v___x_119_);
lean_dec(v_countdown_116_);
lean_dec(v_recur_115_);
lean_dec(v___f_111_);
lean_dec(v_toBind_110_);
lean_dec(v_f_109_);
v___x_123_ = lean_apply_2(v_toPure_108_, lean_box(0), v_acc_113_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v_head_124_ = lean_ctor_get(v_inner_117_, 0);
lean_inc(v_head_124_);
v_tail_125_ = lean_ctor_get(v_inner_117_, 1);
lean_inc(v_tail_125_);
lean_dec_ref_known(v_inner_117_, 2);
v___x_126_ = lean_nat_sub(v_countdown_116_, v___x_121_);
lean_dec(v_countdown_116_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v_tail_125_);
lean_ctor_set(v___x_119_, 0, v___x_126_);
v___x_128_ = v___x_119_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_tail_125_);
v___x_128_ = v_reuseFailAlloc_133_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___f_129_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_129_, 0, v_toPure_108_);
lean_closure_set(v___f_129_, 1, v_recur_115_);
lean_closure_set(v___f_129_, 2, v___x_128_);
v___x_130_ = lean_apply_2(v_f_109_, v_head_124_, v_acc_113_);
lean_inc(v_toBind_110_);
v___x_131_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_130_, v___f_111_);
v___x_132_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_131_, v___f_129_);
return v___x_132_;
}
}
}
else
{
lean_object* v___x_134_; 
lean_del_object(v___x_119_);
lean_dec(v_inner_117_);
lean_dec(v_countdown_116_);
lean_dec(v_recur_115_);
lean_dec(v___f_111_);
lean_dec(v_toBind_110_);
lean_dec(v_f_109_);
v___x_134_ = lean_apply_2(v_toPure_108_, lean_box(0), v_acc_113_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object* v_inst_136_, lean_object* v_00_u03b2_137_, lean_object* v_xs_138_, lean_object* v_init_139_, lean_object* v_f_140_){
_start:
{
lean_object* v___y_142_; lean_object* v_stop_149_; 
v_stop_149_ = lean_ctor_get(v_xs_138_, 1);
if (lean_obj_tag(v_stop_149_) == 0)
{
lean_object* v_list_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_list_150_ = lean_ctor_get(v_xs_138_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_xs_138_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_xs_138_, 1);
lean_dec(v_unused_159_);
v___x_152_ = v_xs_138_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_list_150_);
lean_dec(v_xs_138_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(0u);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v_list_150_);
lean_ctor_set(v___x_152_, 0, v___x_154_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_list_150_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
v___y_142_ = v___x_156_;
goto v___jp_141_;
}
}
}
else
{
lean_object* v_list_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_170_; 
lean_inc_ref(v_stop_149_);
v_list_160_ = lean_ctor_get(v_xs_138_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_xs_138_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v_xs_138_, 1);
lean_dec(v_unused_171_);
v___x_162_ = v_xs_138_;
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_list_160_);
lean_dec(v_xs_138_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_val_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v_val_164_ = lean_ctor_get(v_stop_149_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v_stop_149_, 1);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_val_164_, v___x_165_);
lean_dec(v_val_164_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v_list_160_);
lean_ctor_set(v___x_162_, 0, v___x_166_);
v___x_168_ = v___x_162_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_list_160_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v___y_142_ = v___x_168_;
goto v___jp_141_;
}
}
}
v___jp_141_:
{
lean_object* v_toApplicative_143_; lean_object* v_toBind_144_; lean_object* v_toPure_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_148_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_136_, 0);
lean_inc_ref(v_toApplicative_143_);
v_toBind_144_ = lean_ctor_get(v_inst_136_, 1);
lean_inc(v_toBind_144_);
lean_dec_ref(v_inst_136_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc_n(v_toPure_145_, 2);
lean_dec_ref(v_toApplicative_143_);
v___f_146_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_146_, 0, v_toPure_145_);
v___f_147_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_147_, 0, v_toPure_145_);
lean_closure_set(v___f_147_, 1, v_f_140_);
lean_closure_set(v___f_147_, 2, v_toBind_144_);
lean_closure_set(v___f_147_, 3, v___f_146_);
v___x_148_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_147_, v___y_142_, v_init_139_, lean_box(0));
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object* v_inst_172_){
_start:
{
lean_object* v___f_173_; 
v___f_173_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_173_, 0, v_inst_172_);
return v___f_173_;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object* v_00_u03b1_174_, lean_object* v_m_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___f_177_; 
v___f_177_ = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_177_, 0, v_inst_176_);
return v___f_177_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___lam__0(lean_object* v_it_178_, lean_object* v_acc_179_, lean_object* v_recur_180_){
_start:
{
lean_object* v_countdown_181_; lean_object* v_inner_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_196_; 
v_countdown_181_ = lean_ctor_get(v_it_178_, 0);
v_inner_182_ = lean_ctor_get(v_it_178_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_it_178_);
if (v_isSharedCheck_196_ == 0)
{
v___x_184_ = v_it_178_;
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_inner_182_);
lean_inc(v_countdown_181_);
lean_dec(v_it_178_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_dec_eq(v_countdown_181_, v___x_186_);
if (v___x_187_ == 0)
{
if (lean_obj_tag(v_inner_182_) == 0)
{
lean_del_object(v___x_184_);
lean_dec(v_countdown_181_);
lean_dec_ref(v_recur_180_);
return v_acc_179_;
}
else
{
lean_object* v_head_188_; lean_object* v_tail_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v_head_188_ = lean_ctor_get(v_inner_182_, 0);
lean_inc(v_head_188_);
v_tail_189_ = lean_ctor_get(v_inner_182_, 1);
lean_inc(v_tail_189_);
lean_dec_ref_known(v_inner_182_, 2);
v___x_190_ = lean_nat_sub(v_countdown_181_, v___x_186_);
lean_dec(v_countdown_181_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_tail_189_);
lean_ctor_set(v___x_184_, 0, v___x_190_);
v___x_192_ = v___x_184_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_tail_189_);
v___x_192_ = v_reuseFailAlloc_195_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_array_push(v_acc_179_, v_head_188_);
v___x_194_ = lean_apply_3(v_recur_180_, v___x_192_, v___x_193_, lean_box(0));
return v___x_194_;
}
}
}
else
{
lean_del_object(v___x_184_);
lean_dec(v_inner_182_);
lean_dec(v_countdown_181_);
lean_dec_ref(v_recur_180_);
return v_acc_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___lam__2(lean_object* v___f_199_, lean_object* v___f_200_, lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_214_; lean_object* v_stop_234_; 
v_stop_234_ = lean_ctor_get(v_x_201_, 1);
if (lean_obj_tag(v_stop_234_) == 0)
{
lean_object* v_list_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_list_235_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_x_201_, 1);
lean_dec(v_unused_244_);
v___x_237_ = v_x_201_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_list_235_);
lean_dec(v_x_201_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_unsigned_to_nat(0u);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_list_235_);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_list_235_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v___y_214_ = v___x_241_;
goto v___jp_213_;
}
}
}
else
{
lean_object* v_list_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_255_; 
lean_inc_ref(v_stop_234_);
v_list_245_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; 
v_unused_256_ = lean_ctor_get(v_x_201_, 1);
lean_dec(v_unused_256_);
v___x_247_ = v_x_201_;
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_list_245_);
lean_dec(v_x_201_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_val_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v_val_249_ = lean_ctor_get(v_stop_234_, 0);
lean_inc(v_val_249_);
lean_dec_ref_known(v_stop_234_, 1);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_val_249_, v___x_250_);
lean_dec(v_val_249_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_list_245_);
lean_ctor_set(v___x_247_, 0, v___x_251_);
v___x_253_ = v___x_247_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_list_245_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v___y_214_ = v___x_253_;
goto v___jp_213_;
}
}
}
v___jp_203_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_208_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_199_, v___y_207_, v___y_206_);
v___x_209_ = lean_array_to_list(v___x_208_);
v_a_210_ = l_List_appendTR___redArg(v___y_205_, v___x_209_);
v___x_211_ = l_List_lengthTR___redArg(v_a_210_);
v___x_212_ = l_List_toSlice___redArg(v_a_210_, v___y_204_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v_a_210_);
return v___x_212_;
}
v___jp_213_:
{
lean_object* v_list_215_; lean_object* v_stop_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_233_; 
v_list_215_ = lean_ctor_get(v_y_202_, 0);
v_stop_216_ = lean_ctor_get(v_y_202_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_y_202_);
if (v_isSharedCheck_233_ == 0)
{
v___x_218_ = v_y_202_;
v_isShared_219_ = v_isSharedCheck_233_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_stop_216_);
lean_inc(v_list_215_);
lean_dec(v_y_202_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_233_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = ((lean_object*)(l_List_instAppendListSlice___redArg___lam__2___closed__0));
v___x_222_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_200_, v___y_214_, v___x_221_);
v___x_223_ = lean_array_to_list(v___x_222_);
if (lean_obj_tag(v_stop_216_) == 0)
{
lean_object* v___x_225_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v_list_215_);
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_225_ = v___x_218_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_list_215_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
v___y_204_ = v___x_220_;
v___y_205_ = v___x_223_;
v___y_206_ = v___x_221_;
v___y_207_ = v___x_225_;
goto v___jp_203_;
}
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v_val_227_ = lean_ctor_get(v_stop_216_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v_stop_216_, 1);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_val_227_, v___x_228_);
lean_dec(v_val_227_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v_list_215_);
lean_ctor_set(v___x_218_, 0, v___x_229_);
v___x_231_ = v___x_218_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_list_215_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
v___y_204_ = v___x_220_;
v___y_205_ = v___x_223_;
v___y_206_ = v___x_221_;
v___y_207_ = v___x_231_;
goto v___jp_203_;
}
}
}
}
}
}
lean_object* l_List_instAppendListSlice___redArg(){
_start:
{
lean_object* v___f_261_; 
v___f_261_ = ((lean_object*)(l_List_instAppendListSlice___redArg___closed__1));
return v___f_261_;
}
}
LEAN_EXPORT void l_List_instAppendListSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_262_;
v_res_262_ = l_List_instAppendListSlice___redArg();
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___redArg___boxed(lean_object* v___dummy_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_List_instAppendListSlice___redArg();
return v_res_264_;
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__0(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_List_instAppendListSlice___redArg();
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* v_00_u03b1_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_List_instAppendListSlice___closed__0, &l_List_instAppendListSlice___closed__0_once, _init_l_List_instAppendListSlice___closed__0);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object* v_inst_271_, lean_object* v_s_272_){
_start:
{
lean_object* v_list_273_; lean_object* v_stop_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_299_; 
v_list_273_ = lean_ctor_get(v_s_272_, 0);
v_stop_274_ = lean_ctor_get(v_s_272_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_s_272_);
if (v_isSharedCheck_299_ == 0)
{
v___x_276_ = v_s_272_;
v_isShared_277_ = v_isSharedCheck_299_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_stop_274_);
lean_inc(v_list_273_);
lean_dec(v_s_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_299_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___f_278_; lean_object* v___y_280_; 
v___f_278_ = ((lean_object*)(l_List_instAppendListSlice___redArg___closed__0));
if (lean_obj_tag(v_stop_274_) == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_list_273_);
v___y_280_ = v___x_294_;
goto v___jp_279_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_val_295_ = lean_ctor_get(v_stop_274_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v_stop_274_, 1);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_val_295_, v___x_296_);
lean_dec(v_val_295_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_list_273_);
v___y_280_ = v___x_298_;
goto v___jp_279_;
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_281_ = ((lean_object*)(l_List_instAppendListSlice___redArg___lam__2___closed__0));
v___x_282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_278_, v___y_280_, v___x_281_);
v___x_283_ = lean_array_to_list(v___x_282_);
lean_inc(v___x_283_);
v___x_284_ = l_List_repr___redArg(v_inst_271_, v___x_283_);
v___x_285_ = ((lean_object*)(l_List_ListSlice_repr___redArg___closed__1));
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 5);
lean_ctor_set(v___x_276_, 1, v___x_285_);
lean_ctor_set(v___x_276_, 0, v___x_284_);
v___x_287_ = v___x_276_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_292_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = l_List_lengthTR___redArg(v___x_283_);
lean_dec(v___x_283_);
v___x_289_ = l_Nat_reprFast(v___x_288_);
v___x_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_287_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_s_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_List_ListSlice_repr___redArg(v_inst_301_, v_s_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object* v_inst_304_, lean_object* v_s_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_List_ListSlice_repr___redArg(v_inst_304_, v_s_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object* v_inst_308_, lean_object* v_s_309_, lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_List_instReprListSlice___redArg___lam__0(v_inst_308_, v_s_309_, v_x_310_);
lean_dec(v_x_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object* v_inst_312_){
_start:
{
lean_object* v___f_313_; 
v___f_313_ = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_313_, 0, v_inst_312_);
return v___f_313_;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object* v_00_u03b1_314_, lean_object* v_inst_315_){
_start:
{
lean_object* v___f_316_; 
v___f_316_ = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_316_, 0, v_inst_315_);
return v___f_316_;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object* v___f_318_, lean_object* v_inst_319_, lean_object* v_s_320_){
_start:
{
lean_object* v___y_322_; lean_object* v_stop_329_; 
v_stop_329_ = lean_ctor_get(v_s_320_, 1);
if (lean_obj_tag(v_stop_329_) == 0)
{
lean_object* v_list_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_list_330_ = lean_ctor_get(v_s_320_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_s_320_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v_s_320_, 1);
lean_dec(v_unused_339_);
v___x_332_ = v_s_320_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_list_330_);
lean_dec(v_s_320_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_unsigned_to_nat(0u);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_list_330_);
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_list_330_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v___y_322_ = v___x_336_;
goto v___jp_321_;
}
}
}
else
{
lean_object* v_list_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_350_; 
lean_inc_ref(v_stop_329_);
v_list_340_ = lean_ctor_get(v_s_320_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_s_320_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_s_320_, 1);
lean_dec(v_unused_351_);
v___x_342_ = v_s_320_;
v_isShared_343_ = v_isSharedCheck_350_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_list_340_);
lean_dec(v_s_320_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_350_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_val_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v_val_344_ = lean_ctor_get(v_stop_329_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v_stop_329_, 1);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_val_344_, v___x_345_);
lean_dec(v_val_344_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v_list_340_);
lean_ctor_set(v___x_342_, 0, v___x_346_);
v___x_348_ = v___x_342_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_list_340_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
v___y_322_ = v___x_348_;
goto v___jp_321_;
}
}
}
v___jp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l_List_instAppendListSlice___redArg___lam__2___closed__0));
v___x_324_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_318_, v___y_322_, v___x_323_);
v___x_325_ = ((lean_object*)(l_List_instToStringListSlice___redArg___lam__1___closed__0));
v___x_326_ = lean_array_to_list(v___x_324_);
v___x_327_ = l_List_toString___redArg(v_inst_319_, v___x_326_);
v___x_328_ = lean_string_append(v___x_325_, v___x_327_);
lean_dec_ref(v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* v_inst_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___f_354_; 
v___f_353_ = ((lean_object*)(l_List_instAppendListSlice___redArg___closed__0));
v___f_354_ = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__1), 3, 2);
lean_closure_set(v___f_354_, 0, v___f_353_);
lean_closure_set(v___f_354_, 1, v_inst_352_);
return v___f_354_;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object* v_00_u03b1_355_, lean_object* v_inst_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_List_instToStringListSlice___redArg(v_inst_356_);
return v___x_357_;
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
