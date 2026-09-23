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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg();
return v_res_6_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg();
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(lean_object* v_s_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object* v_s_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v_s_10_);
lean_dec_ref(v_s_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object* v_str_12_, lean_object* v___x_13_, lean_object* v___x_14_, lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
lean_object* v_it_18_; lean_object* v_out_19_; lean_object* v___y_23_; lean_object* v___y_24_; uint32_t v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v_it_33_; lean_object* v_startInclusive_34_; lean_object* v_endExclusive_35_; 
if (lean_obj_tag(v_a_15_) == 0)
{
lean_object* v_currPos_43_; lean_object* v_searcher_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_71_; 
v_currPos_43_ = lean_ctor_get(v_a_15_, 0);
v_searcher_44_ = lean_ctor_get(v_a_15_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_71_ == 0)
{
v___x_46_ = v_a_15_;
v_isShared_47_ = v_isSharedCheck_71_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_searcher_44_);
lean_inc(v_currPos_43_);
lean_dec(v_a_15_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_71_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
uint8_t v___y_49_; uint8_t v_decide_64_; 
v_decide_64_ = lean_nat_dec_eq(v_searcher_44_, v___x_14_);
if (v_decide_64_ == 0)
{
uint32_t v___x_65_; uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_string_utf8_get_fast(v_str_12_, v_searcher_44_);
v___x_66_ = 95;
v___x_67_ = lean_uint32_dec_eq(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 45;
v___x_69_ = lean_uint32_dec_eq(v___x_65_, v___x_68_);
v___y_49_ = v___x_69_;
goto v___jp_48_;
}
else
{
v___y_49_ = v___x_67_;
goto v___jp_48_;
}
}
else
{
lean_object* v___x_70_; 
lean_del_object(v___x_46_);
lean_dec(v_searcher_44_);
v___x_70_ = lean_box(1);
lean_inc(v___x_14_);
v_it_33_ = v___x_70_;
v_startInclusive_34_ = v_currPos_43_;
v_endExclusive_35_ = v___x_14_;
goto v___jp_32_;
}
v___jp_48_:
{
if (v___y_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_string_utf8_next_fast(v_str_12_, v_searcher_44_);
lean_dec(v_searcher_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___x_50_);
v___x_52_ = v___x_46_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_currPos_43_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
v_a_15_ = v___x_52_;
goto _start;
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v_slice_58_; lean_object* v_nextIt_60_; 
v___x_55_ = lean_string_utf8_next_fast(v_str_12_, v_searcher_44_);
v___x_56_ = lean_nat_sub(v___x_55_, v_searcher_44_);
v___x_57_ = lean_nat_add(v_searcher_44_, v___x_56_);
lean_dec(v___x_56_);
v_slice_58_ = l_String_Slice_subslice_x21(v___x_13_, v_currPos_43_, v_searcher_44_);
lean_inc(v___x_57_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___x_57_);
lean_ctor_set(v___x_46_, 0, v___x_57_);
v_nextIt_60_ = v___x_46_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_57_);
v_nextIt_60_ = v_reuseFailAlloc_63_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v_startInclusive_61_; lean_object* v_endExclusive_62_; 
v_startInclusive_61_ = lean_ctor_get(v_slice_58_, 0);
lean_inc(v_startInclusive_61_);
v_endExclusive_62_ = lean_ctor_get(v_slice_58_, 1);
lean_inc(v_endExclusive_62_);
lean_dec_ref(v_slice_58_);
v_it_33_ = v_nextIt_60_;
v_startInclusive_34_ = v_startInclusive_61_;
v_endExclusive_35_ = v_endExclusive_62_;
goto v___jp_32_;
}
}
}
}
}
else
{
lean_dec(v___x_14_);
return v_b_16_;
}
v___jp_17_:
{
lean_object* v___x_20_; 
v___x_20_ = lean_array_push(v_b_16_, v_out_19_);
v_a_15_ = v_it_18_;
v_b_16_ = v___x_20_;
goto _start;
}
v___jp_22_:
{
if (v___y_27_ == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_string_utf8_set(v___y_23_, v___y_26_, v___y_25_);
v_it_18_ = v___y_24_;
v_out_19_ = v___x_28_;
goto v___jp_17_;
}
else
{
uint32_t v___x_29_; uint32_t v___x_30_; lean_object* v___x_31_; 
v___x_29_ = 4294967264;
v___x_30_ = lean_uint32_add(v___y_25_, v___x_29_);
v___x_31_ = lean_string_utf8_set(v___y_23_, v___y_26_, v___x_30_);
v_it_18_ = v___y_24_;
v_out_19_ = v___x_31_;
goto v___jp_17_;
}
}
v___jp_32_:
{
lean_object* v___x_36_; lean_object* v___x_37_; uint32_t v___x_38_; uint32_t v___x_39_; uint8_t v___x_40_; 
v___x_36_ = lean_string_utf8_extract_fast(v_str_12_, v_startInclusive_34_, v_endExclusive_35_);
lean_dec(v_endExclusive_35_);
lean_dec(v_startInclusive_34_);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_string_utf8_get(v___x_36_, v___x_37_);
v___x_39_ = 97;
v___x_40_ = lean_uint32_dec_le(v___x_39_, v___x_38_);
if (v___x_40_ == 0)
{
v___y_23_ = v___x_36_;
v___y_24_ = v_it_33_;
v___y_25_ = v___x_38_;
v___y_26_ = v___x_37_;
v___y_27_ = v___x_40_;
goto v___jp_22_;
}
else
{
uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = 122;
v___x_42_ = lean_uint32_dec_le(v___x_38_, v___x_41_);
v___y_23_ = v___x_36_;
v___y_24_ = v_it_33_;
v___y_25_ = v___x_38_;
v___y_26_ = v___x_37_;
v___y_27_ = v___x_42_;
goto v___jp_22_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg___boxed(lean_object* v_str_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_72_, v___x_73_, v___x_74_, v_a_75_, v_b_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v_str_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
return v_x_78_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___x_82_; 
v_head_80_ = lean_ctor_get(v_x_79_, 0);
v_tail_81_ = lean_ctor_get(v_x_79_, 1);
v___x_82_ = lean_string_append(v_x_78_, v_head_80_);
v_x_78_ = v___x_82_;
v_x_79_ = v_tail_81_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v_x_84_, v_x_85_);
lean_dec(v_x_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object* v_str_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_parts_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_string_utf8_byte_size(v_str_90_);
lean_inc_ref(v_str_90_);
v___x_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_93_, 0, v_str_90_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
v_parts_94_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0);
v___x_95_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__0));
v___x_96_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_90_, v___x_93_, v___x_92_, v_parts_94_, v___x_95_);
lean_dec_ref_known(v___x_93_, 3);
lean_dec_ref(v_str_90_);
v___x_97_ = lean_array_to_list(v___x_96_);
v___x_98_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__1));
v___x_99_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_98_, v___x_97_);
lean_dec(v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* v_str_100_, lean_object* v___x_101_, lean_object* v___x_102_, lean_object* v_inst_103_, lean_object* v_R_104_, lean_object* v_a_105_, lean_object* v_b_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_100_, v___x_101_, v___x_102_, v_a_105_, v_b_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object* v_str_108_, lean_object* v___x_109_, lean_object* v___x_110_, lean_object* v_inst_111_, lean_object* v_R_112_, lean_object* v_a_113_, lean_object* v_b_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(v_str_108_, v___x_109_, v___x_110_, v_inst_111_, v_R_112_, v_a_113_, v_b_114_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v_str_108_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* v_name_116_){
_start:
{
if (lean_obj_tag(v_name_116_) == 1)
{
lean_object* v_pre_117_; lean_object* v_str_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_pre_117_ = lean_ctor_get(v_name_116_, 0);
lean_inc(v_pre_117_);
v_str_118_ = lean_ctor_get(v_name_116_, 1);
lean_inc_ref(v_str_118_);
lean_dec_ref_known(v_name_116_, 2);
v___x_119_ = l_Lake_toUpperCamelCase(v_pre_117_);
v___x_120_ = l_Lake_toUpperCamelCaseString(v_str_118_);
v___x_121_ = l_Lean_Name_str___override(v___x_119_, v___x_120_);
return v___x_121_;
}
else
{
return v_name_116_;
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
