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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5_;
v_res_5_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg();
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___redArg();
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(lean_object* v_s_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v_s_11_);
lean_dec_ref(v_s_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object* v_str_13_, lean_object* v___x_14_, lean_object* v___x_15_, lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
lean_object* v_it_19_; lean_object* v_out_20_; lean_object* v_it_24_; lean_object* v_startInclusive_25_; lean_object* v_endExclusive_26_; 
if (lean_obj_tag(v_a_16_) == 0)
{
lean_object* v_currPos_39_; lean_object* v_searcher_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_67_; 
v_currPos_39_ = lean_ctor_get(v_a_16_, 0);
v_searcher_40_ = lean_ctor_get(v_a_16_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_a_16_);
if (v_isSharedCheck_67_ == 0)
{
v___x_42_ = v_a_16_;
v_isShared_43_ = v_isSharedCheck_67_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_searcher_40_);
lean_inc(v_currPos_39_);
lean_dec(v_a_16_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_67_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
uint8_t v___y_45_; uint8_t v_decide_60_; 
v_decide_60_ = lean_nat_dec_eq(v_searcher_40_, v___x_15_);
if (v_decide_60_ == 0)
{
uint32_t v___x_61_; uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_string_utf8_get_fast(v_str_13_, v_searcher_40_);
v___x_62_ = 95;
v___x_63_ = lean_uint32_dec_eq(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 45;
v___x_65_ = lean_uint32_dec_eq(v___x_61_, v___x_64_);
v___y_45_ = v___x_65_;
goto v___jp_44_;
}
else
{
v___y_45_ = v___x_63_;
goto v___jp_44_;
}
}
else
{
lean_object* v___x_66_; 
lean_del_object(v___x_42_);
lean_dec(v_searcher_40_);
v___x_66_ = lean_box(1);
lean_inc(v___x_15_);
v_it_24_ = v___x_66_;
v_startInclusive_25_ = v_currPos_39_;
v_endExclusive_26_ = v___x_15_;
goto v___jp_23_;
}
v___jp_44_:
{
if (v___y_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = lean_string_utf8_next_fast(v_str_13_, v_searcher_40_);
lean_dec(v_searcher_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_46_);
v___x_48_ = v___x_42_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_currPos_39_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_50_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
v_a_16_ = v___x_48_;
goto _start;
}
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_slice_54_; lean_object* v_nextIt_56_; 
v___x_51_ = lean_string_utf8_next_fast(v_str_13_, v_searcher_40_);
v___x_52_ = lean_nat_sub(v___x_51_, v_searcher_40_);
v___x_53_ = lean_nat_add(v_searcher_40_, v___x_52_);
lean_dec(v___x_52_);
v_slice_54_ = l_String_Slice_subslice_x21(v___x_14_, v_currPos_39_, v_searcher_40_);
lean_inc(v___x_53_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_53_);
lean_ctor_set(v___x_42_, 0, v___x_53_);
v_nextIt_56_ = v___x_42_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___x_53_);
v_nextIt_56_ = v_reuseFailAlloc_59_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v_startInclusive_57_; lean_object* v_endExclusive_58_; 
v_startInclusive_57_ = lean_ctor_get(v_slice_54_, 0);
lean_inc(v_startInclusive_57_);
v_endExclusive_58_ = lean_ctor_get(v_slice_54_, 1);
lean_inc(v_endExclusive_58_);
lean_dec_ref(v_slice_54_);
v_it_24_ = v_nextIt_56_;
v_startInclusive_25_ = v_startInclusive_57_;
v_endExclusive_26_ = v_endExclusive_58_;
goto v___jp_23_;
}
}
}
}
}
else
{
lean_dec(v___x_15_);
return v_b_17_;
}
v___jp_18_:
{
lean_object* v___x_21_; 
v___x_21_ = lean_array_push(v_b_17_, v_out_20_);
v_a_16_ = v_it_19_;
v_b_17_ = v___x_21_;
goto _start;
}
v___jp_23_:
{
lean_object* v___x_27_; lean_object* v___x_28_; uint32_t v___x_29_; uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_27_ = lean_string_utf8_extract_fast(v_str_13_, v_startInclusive_25_, v_endExclusive_26_);
lean_dec(v_endExclusive_26_);
lean_dec(v_startInclusive_25_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_string_utf8_get(v___x_27_, v___x_28_);
v___x_30_ = 97;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v___x_29_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
v___x_32_ = lean_string_utf8_set(v___x_27_, v___x_28_, v___x_29_);
v_it_19_ = v_it_24_;
v_out_20_ = v___x_32_;
goto v___jp_18_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 122;
v___x_34_ = lean_uint32_dec_le(v___x_29_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_string_utf8_set(v___x_27_, v___x_28_, v___x_29_);
v_it_19_ = v_it_24_;
v_out_20_ = v___x_35_;
goto v___jp_18_;
}
else
{
uint32_t v___x_36_; uint32_t v___x_37_; lean_object* v___x_38_; 
v___x_36_ = 4294967264;
v___x_37_ = lean_uint32_add(v___x_29_, v___x_36_);
v___x_38_ = lean_string_utf8_set(v___x_27_, v___x_28_, v___x_37_);
v_it_19_ = v_it_24_;
v_out_20_ = v___x_38_;
goto v___jp_18_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg___boxed(lean_object* v_str_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_68_, v___x_69_, v___x_70_, v_a_71_, v_b_72_);
lean_dec_ref(v___x_69_);
lean_dec_ref(v_str_68_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
return v_x_74_;
}
else
{
lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___x_78_; 
v_head_76_ = lean_ctor_get(v_x_75_, 0);
v_tail_77_ = lean_ctor_get(v_x_75_, 1);
v___x_78_ = lean_string_append(v_x_74_, v_head_76_);
v_x_74_ = v___x_78_;
v_x_75_ = v_tail_77_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v_x_80_, v_x_81_);
lean_dec(v_x_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object* v_str_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_parts_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_string_utf8_byte_size(v_str_86_);
lean_inc_ref(v_str_86_);
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v_str_86_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
v_parts_90_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0);
v___x_91_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__0));
v___x_92_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_86_, v___x_89_, v___x_88_, v_parts_90_, v___x_91_);
lean_dec_ref_known(v___x_89_, 3);
lean_dec_ref(v_str_86_);
v___x_93_ = lean_array_to_list(v___x_92_);
v___x_94_ = ((lean_object*)(l_Lake_toUpperCamelCaseString___closed__1));
v___x_95_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_94_, v___x_93_);
lean_dec(v___x_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* v_str_96_, lean_object* v___x_97_, lean_object* v___x_98_, lean_object* v_inst_99_, lean_object* v_R_100_, lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_96_, v___x_97_, v___x_98_, v_a_101_, v_b_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object* v_str_104_, lean_object* v___x_105_, lean_object* v___x_106_, lean_object* v_inst_107_, lean_object* v_R_108_, lean_object* v_a_109_, lean_object* v_b_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(v_str_104_, v___x_105_, v___x_106_, v_inst_107_, v_R_108_, v_a_109_, v_b_110_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v_str_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* v_name_112_){
_start:
{
if (lean_obj_tag(v_name_112_) == 1)
{
lean_object* v_pre_113_; lean_object* v_str_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_pre_113_ = lean_ctor_get(v_name_112_, 0);
lean_inc(v_pre_113_);
v_str_114_ = lean_ctor_get(v_name_112_, 1);
lean_inc_ref(v_str_114_);
lean_dec_ref_known(v_name_112_, 2);
v___x_115_ = l_Lake_toUpperCamelCase(v_pre_113_);
v___x_116_ = l_Lake_toUpperCamelCaseString(v_str_114_);
v___x_117_ = l_Lean_Name_str___override(v___x_115_, v___x_116_);
return v___x_117_;
}
else
{
return v_name_112_;
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
