// Lean compiler output
// Module: Lake.Util.Casing
// Imports: public import Init.Data.String.Basic import Init.Data.String.Modify import Init.Data.String.Search import Init.Data.Iterators.Consumers.Collect
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_toUpperCamelCaseString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_toUpperCamelCaseString___closed__0 = (const lean_object*)&l_Lake_toUpperCamelCaseString___closed__0_value;
static const lean_string_object l_Lake_toUpperCamelCaseString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_toUpperCamelCaseString___closed__1 = (const lean_object*)&l_Lake_toUpperCamelCaseString___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object* v_s_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v_s_5_);
lean_dec_ref(v_s_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object* v_str_7_, lean_object* v___x_8_, lean_object* v___x_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v_it_13_; lean_object* v_out_14_; lean_object* v_it_18_; lean_object* v_startInclusive_19_; lean_object* v_endExclusive_20_; 
if (lean_obj_tag(v_a_10_) == 0)
{
lean_object* v_currPos_33_; lean_object* v_searcher_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_64_; 
v_currPos_33_ = lean_ctor_get(v_a_10_, 0);
v_searcher_34_ = lean_ctor_get(v_a_10_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_64_ == 0)
{
v___x_36_ = v_a_10_;
v_isShared_37_ = v_isSharedCheck_64_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_searcher_34_);
lean_inc(v_currPos_33_);
lean_dec(v_a_10_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_64_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
uint8_t v___y_39_; lean_object* v_startInclusive_54_; lean_object* v_endExclusive_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_startInclusive_54_ = lean_ctor_get(v___x_8_, 1);
v_endExclusive_55_ = lean_ctor_get(v___x_8_, 2);
v___x_56_ = lean_nat_sub(v_endExclusive_55_, v_startInclusive_54_);
v___x_57_ = lean_nat_dec_eq(v_searcher_34_, v___x_56_);
lean_dec(v___x_56_);
if (v___x_57_ == 0)
{
uint32_t v___x_58_; uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lean_string_utf8_get_fast(v_str_7_, v_searcher_34_);
v___x_59_ = 95;
v___x_60_ = lean_uint32_dec_eq(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 45;
v___x_62_ = lean_uint32_dec_eq(v___x_58_, v___x_61_);
v___y_39_ = v___x_62_;
goto v___jp_38_;
}
else
{
v___y_39_ = v___x_60_;
goto v___jp_38_;
}
}
else
{
lean_object* v___x_63_; 
lean_del_object(v___x_36_);
lean_dec(v_searcher_34_);
v___x_63_ = lean_box(1);
lean_inc(v___x_9_);
v_it_18_ = v___x_63_;
v_startInclusive_19_ = v_currPos_33_;
v_endExclusive_20_ = v___x_9_;
goto v___jp_17_;
}
v___jp_38_:
{
if (v___y_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = lean_string_utf8_next_fast(v_str_7_, v_searcher_34_);
lean_dec(v_searcher_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_40_);
v___x_42_ = v___x_36_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_currPos_33_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
v_a_10_ = v___x_42_;
goto _start;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v_slice_48_; lean_object* v_nextIt_50_; 
v___x_45_ = lean_string_utf8_next_fast(v_str_7_, v_searcher_34_);
v___x_46_ = lean_nat_sub(v___x_45_, v_searcher_34_);
v___x_47_ = lean_nat_add(v_searcher_34_, v___x_46_);
lean_dec(v___x_46_);
v_slice_48_ = l_String_Slice_subslice_x21(v___x_8_, v_currPos_33_, v_searcher_34_);
lean_inc(v___x_47_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_47_);
lean_ctor_set(v___x_36_, 0, v___x_47_);
v_nextIt_50_ = v___x_36_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_47_);
v_nextIt_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v_startInclusive_51_; lean_object* v_endExclusive_52_; 
v_startInclusive_51_ = lean_ctor_get(v_slice_48_, 0);
lean_inc(v_startInclusive_51_);
v_endExclusive_52_ = lean_ctor_get(v_slice_48_, 1);
lean_inc(v_endExclusive_52_);
lean_dec_ref(v_slice_48_);
v_it_18_ = v_nextIt_50_;
v_startInclusive_19_ = v_startInclusive_51_;
v_endExclusive_20_ = v_endExclusive_52_;
goto v___jp_17_;
}
}
}
}
}
else
{
lean_dec(v___x_9_);
return v_b_11_;
}
v___jp_12_:
{
lean_object* v___x_15_; 
v___x_15_ = lean_array_push(v_b_11_, v_out_14_);
v_a_10_ = v_it_13_;
v_b_11_ = v___x_15_;
goto _start;
}
v___jp_17_:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint32_t v___x_23_; uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_21_ = lean_string_utf8_extract(v_str_7_, v_startInclusive_19_, v_endExclusive_20_);
lean_dec(v_endExclusive_20_);
lean_dec(v_startInclusive_19_);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_string_utf8_get(v___x_21_, v___x_22_);
v___x_24_ = 97;
v___x_25_ = lean_uint32_dec_le(v___x_24_, v___x_23_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_string_utf8_set(v___x_21_, v___x_22_, v___x_23_);
v_it_13_ = v_it_18_;
v_out_14_ = v___x_26_;
goto v___jp_12_;
}
else
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 122;
v___x_28_ = lean_uint32_dec_le(v___x_23_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
v___x_29_ = lean_string_utf8_set(v___x_21_, v___x_22_, v___x_23_);
v_it_13_ = v_it_18_;
v_out_14_ = v___x_29_;
goto v___jp_12_;
}
else
{
uint32_t v___x_30_; uint32_t v___x_31_; lean_object* v___x_32_; 
v___x_30_ = 4294967264;
v___x_31_ = lean_uint32_add(v___x_23_, v___x_30_);
v___x_32_ = lean_string_utf8_set(v___x_21_, v___x_22_, v___x_31_);
v_it_13_ = v_it_18_;
v_out_14_ = v___x_32_;
goto v___jp_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg___boxed(lean_object* v_str_65_, lean_object* v___x_66_, lean_object* v___x_67_, lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_65_, v___x_66_, v___x_67_, v_a_68_, v_b_69_);
lean_dec_ref(v___x_66_);
lean_dec_ref(v_str_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
return v_x_71_;
}
else
{
lean_object* v_head_73_; lean_object* v_tail_74_; lean_object* v___x_75_; 
v_head_73_ = lean_ctor_get(v_x_72_, 0);
v_tail_74_ = lean_ctor_get(v_x_72_, 1);
v___x_75_ = lean_string_append(v_x_71_, v_head_73_);
v_x_71_ = v___x_75_;
v_x_72_ = v_tail_74_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v_x_77_, v_x_78_);
lean_dec(v_x_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object* v_str_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_parts_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_string_utf8_byte_size(v_str_83_);
lean_inc_ref(v_str_83_);
v___x_86_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_86_, 0, v_str_83_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_85_);
v_parts_87_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v___x_86_);
v___x_88_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__0));
v___x_89_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_83_, v___x_86_, v___x_85_, v_parts_87_, v___x_88_);
lean_dec_ref(v___x_86_);
lean_dec_ref(v_str_83_);
v___x_90_ = lean_array_to_list(v___x_89_);
v___x_91_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__1));
v___x_92_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_91_, v___x_90_);
lean_dec(v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* v_str_93_, lean_object* v___x_94_, lean_object* v___x_95_, lean_object* v_inst_96_, lean_object* v_R_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_93_, v___x_94_, v___x_95_, v_a_98_, v_b_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object* v_str_101_, lean_object* v___x_102_, lean_object* v___x_103_, lean_object* v_inst_104_, lean_object* v_R_105_, lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(v_str_101_, v___x_102_, v___x_103_, v_inst_104_, v_R_105_, v_a_106_, v_b_107_);
lean_dec_ref(v___x_102_);
lean_dec_ref(v_str_101_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* v_name_109_){
_start:
{
if (lean_obj_tag(v_name_109_) == 1)
{
lean_object* v_pre_110_; lean_object* v_str_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_pre_110_ = lean_ctor_get(v_name_109_, 0);
lean_inc(v_pre_110_);
v_str_111_ = lean_ctor_get(v_name_109_, 1);
lean_inc_ref(v_str_111_);
lean_dec_ref(v_name_109_);
v___x_112_ = l_Lake_toUpperCamelCase(v_pre_110_);
v___x_113_ = l_Lake_toUpperCamelCaseString(v_str_111_);
v___x_114_ = l_Lean_Name_str___override(v___x_112_, v___x_113_);
return v___x_114_;
}
else
{
return v_name_109_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Casing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Casing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Casing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Casing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Casing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Casing(builtin);
}
#ifdef __cplusplus
}
#endif
