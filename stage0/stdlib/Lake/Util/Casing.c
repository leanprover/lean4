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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_object* v_it_13_; lean_object* v_out_14_; lean_object* v___y_18_; lean_object* v___y_19_; uint32_t v___y_20_; lean_object* v___y_21_; uint8_t v___y_22_; lean_object* v_it_28_; lean_object* v_startInclusive_29_; lean_object* v_endExclusive_30_; 
if (lean_obj_tag(v_a_10_) == 0)
{
lean_object* v_currPos_38_; lean_object* v_searcher_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_66_; 
v_currPos_38_ = lean_ctor_get(v_a_10_, 0);
v_searcher_39_ = lean_ctor_get(v_a_10_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_66_ == 0)
{
v___x_41_ = v_a_10_;
v_isShared_42_ = v_isSharedCheck_66_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_searcher_39_);
lean_inc(v_currPos_38_);
lean_dec(v_a_10_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_66_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
uint8_t v___y_44_; uint8_t v_decide_59_; 
v_decide_59_ = lean_nat_dec_eq(v_searcher_39_, v___x_9_);
if (v_decide_59_ == 0)
{
uint32_t v___x_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_60_ = lean_string_utf8_get_fast(v_str_7_, v_searcher_39_);
v___x_61_ = 95;
v___x_62_ = lean_uint32_dec_eq(v___x_60_, v___x_61_);
if (v___x_62_ == 0)
{
uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_63_ = 45;
v___x_64_ = lean_uint32_dec_eq(v___x_60_, v___x_63_);
v___y_44_ = v___x_64_;
goto v___jp_43_;
}
else
{
v___y_44_ = v___x_62_;
goto v___jp_43_;
}
}
else
{
lean_object* v___x_65_; 
lean_del_object(v___x_41_);
lean_dec(v_searcher_39_);
v___x_65_ = lean_box(1);
lean_inc(v___x_9_);
v_it_28_ = v___x_65_;
v_startInclusive_29_ = v_currPos_38_;
v_endExclusive_30_ = v___x_9_;
goto v___jp_27_;
}
v___jp_43_:
{
if (v___y_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_45_ = lean_string_utf8_next_fast(v_str_7_, v_searcher_39_);
lean_dec(v_searcher_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_45_);
v___x_47_ = v___x_41_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_currPos_38_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_45_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
v_a_10_ = v___x_47_;
goto _start;
}
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v_slice_53_; lean_object* v_nextIt_55_; 
v___x_50_ = lean_string_utf8_next_fast(v_str_7_, v_searcher_39_);
v___x_51_ = lean_nat_sub(v___x_50_, v_searcher_39_);
v___x_52_ = lean_nat_add(v_searcher_39_, v___x_51_);
lean_dec(v___x_51_);
v_slice_53_ = l_String_Slice_subslice_x21(v___x_8_, v_currPos_38_, v_searcher_39_);
lean_inc(v___x_52_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_52_);
lean_ctor_set(v___x_41_, 0, v___x_52_);
v_nextIt_55_ = v___x_41_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_52_);
v_nextIt_55_ = v_reuseFailAlloc_58_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v_startInclusive_56_; lean_object* v_endExclusive_57_; 
v_startInclusive_56_ = lean_ctor_get(v_slice_53_, 0);
lean_inc(v_startInclusive_56_);
v_endExclusive_57_ = lean_ctor_get(v_slice_53_, 1);
lean_inc(v_endExclusive_57_);
lean_dec_ref(v_slice_53_);
v_it_28_ = v_nextIt_55_;
v_startInclusive_29_ = v_startInclusive_56_;
v_endExclusive_30_ = v_endExclusive_57_;
goto v___jp_27_;
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
if (v___y_22_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_string_utf8_set(v___y_18_, v___y_21_, v___y_20_);
v_it_13_ = v___y_19_;
v_out_14_ = v___x_23_;
goto v___jp_12_;
}
else
{
uint32_t v___x_24_; uint32_t v___x_25_; lean_object* v___x_26_; 
v___x_24_ = 4294967264;
v___x_25_ = lean_uint32_add(v___y_20_, v___x_24_);
v___x_26_ = lean_string_utf8_set(v___y_18_, v___y_21_, v___x_25_);
v_it_13_ = v___y_19_;
v_out_14_ = v___x_26_;
goto v___jp_12_;
}
}
v___jp_27_:
{
lean_object* v___x_31_; lean_object* v___x_32_; uint32_t v___x_33_; uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_31_ = lean_string_utf8_extract_fast(v_str_7_, v_startInclusive_29_, v_endExclusive_30_);
lean_dec(v_endExclusive_30_);
lean_dec(v_startInclusive_29_);
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_string_utf8_get(v___x_31_, v___x_32_);
v___x_34_ = 97;
v___x_35_ = lean_uint32_dec_le(v___x_34_, v___x_33_);
if (v___x_35_ == 0)
{
v___y_18_ = v___x_31_;
v___y_19_ = v_it_28_;
v___y_20_ = v___x_33_;
v___y_21_ = v___x_32_;
v___y_22_ = v___x_35_;
goto v___jp_17_;
}
else
{
uint32_t v___x_36_; uint8_t v___x_37_; 
v___x_36_ = 122;
v___x_37_ = lean_uint32_dec_le(v___x_33_, v___x_36_);
v___y_18_ = v___x_31_;
v___y_19_ = v_it_28_;
v___y_20_ = v___x_33_;
v___y_21_ = v___x_32_;
v___y_22_ = v___x_37_;
goto v___jp_17_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg___boxed(lean_object* v_str_67_, lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_67_, v___x_68_, v___x_69_, v_a_70_, v_b_71_);
lean_dec_ref(v___x_68_);
lean_dec_ref(v_str_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
return v_x_73_;
}
else
{
lean_object* v_head_75_; lean_object* v_tail_76_; lean_object* v___x_77_; 
v_head_75_ = lean_ctor_get(v_x_74_, 0);
v_tail_76_ = lean_ctor_get(v_x_74_, 1);
v___x_77_ = lean_string_append(v_x_73_, v_head_75_);
v_x_73_ = v___x_77_;
v_x_74_ = v_tail_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v_x_79_, v_x_80_);
lean_dec(v_x_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object* v_str_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_parts_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_string_utf8_byte_size(v_str_85_);
lean_inc_ref(v_str_85_);
v___x_88_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_88_, 0, v_str_85_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
v_parts_89_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v___x_88_);
v___x_90_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__0));
v___x_91_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_85_, v___x_88_, v___x_87_, v_parts_89_, v___x_90_);
lean_dec_ref_known(v___x_88_, 3);
lean_dec_ref(v_str_85_);
v___x_92_ = lean_array_to_list(v___x_91_);
v___x_93_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__1));
v___x_94_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_93_, v___x_92_);
lean_dec(v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* v_str_95_, lean_object* v___x_96_, lean_object* v___x_97_, lean_object* v_inst_98_, lean_object* v_R_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_95_, v___x_96_, v___x_97_, v_a_100_, v_b_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object* v_str_103_, lean_object* v___x_104_, lean_object* v___x_105_, lean_object* v_inst_106_, lean_object* v_R_107_, lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(v_str_103_, v___x_104_, v___x_105_, v_inst_106_, v_R_107_, v_a_108_, v_b_109_);
lean_dec_ref(v___x_104_);
lean_dec_ref(v_str_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* v_name_111_){
_start:
{
if (lean_obj_tag(v_name_111_) == 1)
{
lean_object* v_pre_112_; lean_object* v_str_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_pre_112_ = lean_ctor_get(v_name_111_, 0);
lean_inc(v_pre_112_);
v_str_113_ = lean_ctor_get(v_name_111_, 1);
lean_inc_ref(v_str_113_);
lean_dec_ref_known(v_name_111_, 2);
v___x_114_ = l_Lake_toUpperCamelCase(v_pre_112_);
v___x_115_ = l_Lake_toUpperCamelCaseString(v_str_113_);
v___x_116_ = l_Lean_Name_str___override(v___x_114_, v___x_115_);
return v___x_116_;
}
else
{
return v_name_111_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Casing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
