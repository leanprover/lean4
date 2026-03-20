// Lean compiler output
// Module: Init.Data.Format.Instances
// Imports: import Init.Data.String.Search public import Init.Data.ToString.Basic import Init.Data.Iterators.Consumers.Collect
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
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg___lam__0(lean_object*);
static const lean_closure_object l_instToFormatOfToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToFormatOfToString___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToFormatOfToString___redArg___closed__0 = (const lean_object*)&l_instToFormatOfToString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOfToString(lean_object*, lean_object*);
static const lean_string_object l_List_format___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_format___redArg___closed__0 = (const lean_object*)&l_List_format___redArg___closed__0_value;
static const lean_ctor_object l_List_format___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_format___redArg___closed__0_value)}};
static const lean_object* l_List_format___redArg___closed__1 = (const lean_object*)&l_List_format___redArg___closed__1_value;
static const lean_string_object l_List_format___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_format___redArg___closed__2 = (const lean_object*)&l_List_format___redArg___closed__2_value;
static const lean_ctor_object l_List_format___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_format___redArg___closed__2_value)}};
static const lean_object* l_List_format___redArg___closed__3 = (const lean_object*)&l_List_format___redArg___closed__3_value;
static const lean_ctor_object l_List_format___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_format___redArg___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_format___redArg___closed__4 = (const lean_object*)&l_List_format___redArg___closed__4_value;
static const lean_string_object l_List_format___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_format___redArg___closed__5 = (const lean_object*)&l_List_format___redArg___closed__5_value;
static const lean_string_object l_List_format___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_format___redArg___closed__6 = (const lean_object*)&l_List_format___redArg___closed__6_value;
static lean_once_cell_t l_List_format___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_format___redArg___closed__7;
static lean_once_cell_t l_List_format___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_format___redArg___closed__8;
static const lean_ctor_object l_List_format___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_format___redArg___closed__5_value)}};
static const lean_object* l_List_format___redArg___closed__9 = (const lean_object*)&l_List_format___redArg___closed__9_value;
static const lean_ctor_object l_List_format___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_format___redArg___closed__6_value)}};
static const lean_object* l_List_format___redArg___closed__10 = (const lean_object*)&l_List_format___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_format___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatList(lean_object*, lean_object*);
static const lean_string_object l_instToFormatArray___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_instToFormatArray___redArg___lam__0___closed__0 = (const lean_object*)&l_instToFormatArray___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_instToFormatArray___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instToFormatArray___redArg___lam__0___closed__0_value)}};
static const lean_object* l_instToFormatArray___redArg___lam__0___closed__1 = (const lean_object*)&l_instToFormatArray___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToFormatArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatArray(lean_object*, lean_object*);
static const lean_string_object l_Option_format___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_format___redArg___closed__0 = (const lean_object*)&l_Option_format___redArg___closed__0_value;
static const lean_ctor_object l_Option_format___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_format___redArg___closed__0_value)}};
static const lean_object* l_Option_format___redArg___closed__1 = (const lean_object*)&l_Option_format___redArg___closed__1_value;
static const lean_string_object l_Option_format___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_format___redArg___closed__2 = (const lean_object*)&l_Option_format___redArg___closed__2_value;
static const lean_ctor_object l_Option_format___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_format___redArg___closed__2_value)}};
static const lean_object* l_Option_format___redArg___closed__3 = (const lean_object*)&l_Option_format___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Option_format___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOption(lean_object*, lean_object*);
static const lean_string_object l_instToFormatProd___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_instToFormatProd___redArg___lam__0___closed__0 = (const lean_object*)&l_instToFormatProd___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToFormatProd___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_instToFormatProd___redArg___lam__0___closed__1 = (const lean_object*)&l_instToFormatProd___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_instToFormatProd___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToFormatProd___redArg___lam__0___closed__2;
static lean_once_cell_t l_instToFormatProd___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToFormatProd___redArg___lam__0___closed__3;
static const lean_ctor_object l_instToFormatProd___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instToFormatProd___redArg___lam__0___closed__0_value)}};
static const lean_object* l_instToFormatProd___redArg___lam__0___closed__4 = (const lean_object*)&l_instToFormatProd___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_instToFormatProd___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instToFormatProd___redArg___lam__0___closed__1_value)}};
static const lean_object* l_instToFormatProd___redArg___lam__0___closed__5 = (const lean_object*)&l_instToFormatProd___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_instToFormatProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00String_toFormat_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00String_toFormat_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_String_toFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_String_toFormat___closed__0 = (const lean_object*)&l_String_toFormat___closed__0_value;
LEAN_EXPORT lean_object* l_String_toFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatRaw___lam__0(lean_object*);
static const lean_closure_object l_instToFormatRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToFormatRaw___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToFormatRaw___closed__0 = (const lean_object*)&l_instToFormatRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_instToFormatRaw = (const lean_object*)&l_instToFormatRaw___closed__0_value;
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg___lam__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2_, 0, v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg(lean_object* v_inst_4_){
_start:
{
lean_object* v___f_5_; lean_object* v___x_6_; 
v___f_5_ = ((lean_object*)(l_instToFormatOfToString___redArg___closed__0));
v___x_6_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_6_, 0, lean_box(0));
lean_closure_set(v___x_6_, 1, lean_box(0));
lean_closure_set(v___x_6_, 2, lean_box(0));
lean_closure_set(v___x_6_, 3, v___f_5_);
lean_closure_set(v___x_6_, 4, v_inst_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_instToFormatOfToString(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_instToFormatOfToString___redArg(v_inst_8_);
return v___x_9_;
}
}
static lean_object* _init_l_List_format___redArg___closed__7(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_List_format___redArg___closed__5));
v___x_22_ = lean_string_length(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_List_format___redArg___closed__8(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_obj_once(&l_List_format___redArg___closed__7, &l_List_format___redArg___closed__7_once, _init_l_List_format___redArg___closed__7);
v___x_24_ = lean_nat_to_int(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_List_format___redArg(lean_object* v_inst_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_31_; 
lean_dec_ref(v_inst_29_);
v___x_31_ = ((lean_object*)(l_List_format___redArg___closed__1));
return v___x_31_;
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; lean_object* v___x_41_; 
v___x_32_ = ((lean_object*)(l_List_format___redArg___closed__4));
v___x_33_ = l_Std_Format_joinSep___redArg(v_inst_29_, v_x_30_, v___x_32_);
v___x_34_ = lean_obj_once(&l_List_format___redArg___closed__8, &l_List_format___redArg___closed__8_once, _init_l_List_format___redArg___closed__8);
v___x_35_ = ((lean_object*)(l_List_format___redArg___closed__9));
v___x_36_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_33_);
v___x_37_ = ((lean_object*)(l_List_format___redArg___closed__10));
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_34_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = 0;
v___x_41_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_41_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_41_, sizeof(void*)*1, v___x_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_List_format(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_List_format___redArg(v_inst_43_, v_x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_instToFormatList___redArg(lean_object* v_inst_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_alloc_closure((void*)(l_List_format), 3, 2);
lean_closure_set(v___x_47_, 0, lean_box(0));
lean_closure_set(v___x_47_, 1, v_inst_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_instToFormatList(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_alloc_closure((void*)(l_List_format), 3, 2);
lean_closure_set(v___x_50_, 0, lean_box(0));
lean_closure_set(v___x_50_, 1, v_inst_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_instToFormatArray___redArg___lam__0(lean_object* v_inst_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l_instToFormatArray___redArg___lam__0___closed__1));
v___x_57_ = lean_array_to_list(v_a_55_);
v___x_58_ = l_List_format___redArg(v_inst_54_, v___x_57_);
v___x_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_56_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_instToFormatArray___redArg(lean_object* v_inst_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = lean_alloc_closure((void*)(l_instToFormatArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_61_, 0, v_inst_60_);
return v___f_61_;
}
}
LEAN_EXPORT lean_object* l_instToFormatArray(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v___f_64_; 
v___f_64_ = lean_alloc_closure((void*)(l_instToFormatArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_64_, 0, v_inst_63_);
return v___f_64_;
}
}
LEAN_EXPORT lean_object* l_Option_format___redArg(lean_object* v_inst_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v___x_73_; 
lean_dec_ref(v_inst_71_);
v___x_73_ = ((lean_object*)(l_Option_format___redArg___closed__1));
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_val_74_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_val_74_);
lean_dec_ref(v_x_72_);
v___x_75_ = ((lean_object*)(l_Option_format___redArg___closed__3));
v___x_76_ = lean_apply_1(v_inst_71_, v_val_74_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Option_format(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Option_format___redArg(v_inst_79_, v_x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_instToFormatOption___redArg(lean_object* v_inst_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_closure((void*)(l_Option_format), 3, 2);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, v_inst_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_instToFormatOption(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_alloc_closure((void*)(l_Option_format), 3, 2);
lean_closure_set(v___x_86_, 0, lean_box(0));
lean_closure_set(v___x_86_, 1, v_inst_85_);
return v___x_86_;
}
}
static lean_object* _init_l_instToFormatProd___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_instToFormatProd___redArg___lam__0___closed__0));
v___x_90_ = lean_string_length(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_instToFormatProd___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l_instToFormatProd___redArg___lam__0___closed__2, &l_instToFormatProd___redArg___lam__0___closed__2_once, _init_l_instToFormatProd___redArg___lam__0___closed__2);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_instToFormatProd___redArg___lam__0(lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_fst_100_; lean_object* v_snd_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_122_; 
v_fst_100_ = lean_ctor_get(v_x_99_, 0);
v_snd_101_ = lean_ctor_get(v_x_99_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_122_ == 0)
{
v___x_103_ = v_x_99_;
v_isShared_104_ = v_isSharedCheck_122_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_snd_101_);
lean_inc(v_fst_100_);
lean_dec(v_x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_122_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_105_ = lean_apply_1(v_inst_97_, v_fst_100_);
v___x_106_ = ((lean_object*)(l_List_format___redArg___closed__3));
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 5);
lean_ctor_set(v___x_103_, 1, v___x_106_);
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_121_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; 
v___x_109_ = lean_box(1);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_apply_1(v_inst_98_, v_snd_101_);
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_obj_once(&l_instToFormatProd___redArg___lam__0___closed__3, &l_instToFormatProd___redArg___lam__0___closed__3_once, _init_l_instToFormatProd___redArg___lam__0___closed__3);
v___x_114_ = ((lean_object*)(l_instToFormatProd___redArg___lam__0___closed__4));
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_112_);
v___x_116_ = ((lean_object*)(l_instToFormatProd___redArg___lam__0___closed__5));
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_113_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_instToFormatProd___redArg(lean_object* v_inst_123_, lean_object* v_inst_124_){
_start:
{
lean_object* v___f_125_; 
v___f_125_ = lean_alloc_closure((void*)(l_instToFormatProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_125_, 0, v_inst_123_);
lean_closure_set(v___f_125_, 1, v_inst_124_);
return v___f_125_;
}
}
LEAN_EXPORT lean_object* l_instToFormatProd(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = lean_alloc_closure((void*)(l_instToFormatProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_130_, 0, v_inst_128_);
lean_closure_set(v___f_130_, 1, v_inst_129_);
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(lean_object* v_s_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0));
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___boxed(lean_object* v_s_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(v_s_135_);
lean_dec_ref(v_s_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00String_toFormat_spec__2_spec__2(lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_dec(v_x_137_);
return v_x_138_;
}
else
{
lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_155_; 
v_head_140_ = lean_ctor_get(v_x_139_, 0);
v_tail_141_ = lean_ctor_get(v_x_139_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_155_ == 0)
{
v___x_143_ = v_x_139_;
v_isShared_144_ = v_isSharedCheck_155_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_tail_141_);
lean_inc(v_head_140_);
lean_dec(v_x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_155_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_str_145_; lean_object* v_startInclusive_146_; lean_object* v_endExclusive_147_; lean_object* v___x_149_; 
v_str_145_ = lean_ctor_get(v_head_140_, 0);
lean_inc_ref(v_str_145_);
v_startInclusive_146_ = lean_ctor_get(v_head_140_, 1);
lean_inc(v_startInclusive_146_);
v_endExclusive_147_ = lean_ctor_get(v_head_140_, 2);
lean_inc(v_endExclusive_147_);
lean_dec(v_head_140_);
lean_inc(v_x_137_);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 5);
lean_ctor_set(v___x_143_, 1, v_x_137_);
lean_ctor_set(v___x_143_, 0, v_x_138_);
v___x_149_ = v___x_143_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_x_138_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_x_137_);
v___x_149_ = v_reuseFailAlloc_154_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_string_utf8_extract(v_str_145_, v_startInclusive_146_, v_endExclusive_147_);
lean_dec(v_endExclusive_147_);
lean_dec(v_startInclusive_146_);
lean_dec_ref(v_str_145_);
v___x_151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_149_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v_x_138_ = v___x_152_;
v_x_139_ = v_tail_141_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00String_toFormat_spec__2(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_158_; 
lean_dec(v_x_157_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v_tail_159_; 
v_tail_159_ = lean_ctor_get(v_x_156_, 1);
if (lean_obj_tag(v_tail_159_) == 0)
{
lean_object* v_head_160_; lean_object* v_str_161_; lean_object* v_startInclusive_162_; lean_object* v_endExclusive_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_x_157_);
v_head_160_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_160_);
lean_dec_ref(v_x_156_);
v_str_161_ = lean_ctor_get(v_head_160_, 0);
lean_inc_ref(v_str_161_);
v_startInclusive_162_ = lean_ctor_get(v_head_160_, 1);
lean_inc(v_startInclusive_162_);
v_endExclusive_163_ = lean_ctor_get(v_head_160_, 2);
lean_inc(v_endExclusive_163_);
lean_dec(v_head_160_);
v___x_164_ = lean_string_utf8_extract(v_str_161_, v_startInclusive_162_, v_endExclusive_163_);
lean_dec(v_endExclusive_163_);
lean_dec(v_startInclusive_162_);
lean_dec_ref(v_str_161_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_head_166_; lean_object* v_str_167_; lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc(v_tail_159_);
v_head_166_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_166_);
lean_dec_ref(v_x_156_);
v_str_167_ = lean_ctor_get(v_head_166_, 0);
lean_inc_ref(v_str_167_);
v_startInclusive_168_ = lean_ctor_get(v_head_166_, 1);
lean_inc(v_startInclusive_168_);
v_endExclusive_169_ = lean_ctor_get(v_head_166_, 2);
lean_inc(v_endExclusive_169_);
lean_dec(v_head_166_);
v___x_170_ = lean_string_utf8_extract(v_str_167_, v_startInclusive_168_, v_endExclusive_169_);
lean_dec(v_endExclusive_169_);
lean_dec(v_startInclusive_168_);
lean_dec_ref(v_str_167_);
v___x_171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___x_172_ = l_List_foldl___at___00Std_Format_joinSep___at___00String_toFormat_spec__2_spec__2(v_x_157_, v___x_171_, v_tail_159_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(lean_object* v_s_173_, lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_it_179_; lean_object* v_startInclusive_180_; lean_object* v_endExclusive_181_; 
if (lean_obj_tag(v_a_176_) == 0)
{
lean_object* v_currPos_185_; lean_object* v_searcher_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_212_; 
v_currPos_185_ = lean_ctor_get(v_a_176_, 0);
v_searcher_186_ = lean_ctor_get(v_a_176_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_212_ == 0)
{
v___x_188_ = v_a_176_;
v_isShared_189_ = v_isSharedCheck_212_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_searcher_186_);
lean_inc(v_currPos_185_);
lean_dec(v_a_176_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_212_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_startInclusive_190_; lean_object* v_endExclusive_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_startInclusive_190_ = lean_ctor_get(v___x_174_, 1);
v_endExclusive_191_ = lean_ctor_get(v___x_174_, 2);
v___x_192_ = lean_nat_sub(v_endExclusive_191_, v_startInclusive_190_);
v___x_193_ = lean_nat_dec_eq(v_searcher_186_, v___x_192_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
uint32_t v___x_194_; uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = 10;
v___x_195_ = lean_string_utf8_get_fast(v_s_173_, v_searcher_186_);
v___x_196_ = lean_uint32_dec_eq(v___x_195_, v___x_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_string_utf8_next_fast(v_s_173_, v_searcher_186_);
lean_dec(v_searcher_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_197_);
v___x_199_ = v___x_188_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_currPos_185_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_197_);
v___x_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
v_a_176_ = v___x_199_;
goto _start;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_slice_205_; lean_object* v_nextIt_207_; 
v___x_202_ = lean_string_utf8_next_fast(v_s_173_, v_searcher_186_);
v___x_203_ = lean_nat_sub(v___x_202_, v_searcher_186_);
v___x_204_ = lean_nat_add(v_searcher_186_, v___x_203_);
lean_dec(v___x_203_);
v_slice_205_ = l_String_Slice_subslice_x21(v___x_174_, v_currPos_185_, v_searcher_186_);
lean_inc(v___x_204_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_204_);
lean_ctor_set(v___x_188_, 0, v___x_204_);
v_nextIt_207_ = v___x_188_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_204_);
v_nextIt_207_ = v_reuseFailAlloc_210_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v_startInclusive_208_; lean_object* v_endExclusive_209_; 
v_startInclusive_208_ = lean_ctor_get(v_slice_205_, 0);
lean_inc(v_startInclusive_208_);
v_endExclusive_209_ = lean_ctor_get(v_slice_205_, 1);
lean_inc(v_endExclusive_209_);
lean_dec_ref(v_slice_205_);
v_it_179_ = v_nextIt_207_;
v_startInclusive_180_ = v_startInclusive_208_;
v_endExclusive_181_ = v_endExclusive_209_;
goto v___jp_178_;
}
}
}
else
{
lean_object* v___x_211_; 
lean_del_object(v___x_188_);
lean_dec(v_searcher_186_);
v___x_211_ = lean_box(1);
lean_inc(v___x_175_);
v_it_179_ = v___x_211_;
v_startInclusive_180_ = v_currPos_185_;
v_endExclusive_181_ = v___x_175_;
goto v___jp_178_;
}
}
}
else
{
lean_dec(v___x_175_);
lean_dec_ref(v_s_173_);
return v_b_177_;
}
v___jp_178_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc_ref(v_s_173_);
v___x_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_182_, 0, v_s_173_);
lean_ctor_set(v___x_182_, 1, v_startInclusive_180_);
lean_ctor_set(v___x_182_, 2, v_endExclusive_181_);
v___x_183_ = lean_array_push(v_b_177_, v___x_182_);
v_a_176_ = v_it_179_;
v_b_177_ = v___x_183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg___boxed(lean_object* v_s_213_, lean_object* v___x_214_, lean_object* v___x_215_, lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_213_, v___x_214_, v___x_215_, v_a_216_, v_b_217_);
lean_dec_ref(v___x_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_String_toFormat(lean_object* v_s_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_string_utf8_byte_size(v_s_221_);
lean_inc_ref(v_s_221_);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v_s_221_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_223_);
v___x_225_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(v___x_224_);
v___x_226_ = ((lean_object*)(l_String_toFormat___closed__0));
v___x_227_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_221_, v___x_224_, v___x_223_, v___x_225_, v___x_226_);
lean_dec_ref(v___x_224_);
v___x_228_ = lean_array_to_list(v___x_227_);
v___x_229_ = lean_box(1);
v___x_230_ = l_Std_Format_joinSep___at___00String_toFormat_spec__2(v___x_228_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(lean_object* v_s_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v_inst_234_, lean_object* v_R_235_, lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_231_, v___x_232_, v___x_233_, v_a_236_, v_b_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___boxed(lean_object* v_s_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v_inst_242_, lean_object* v_R_243_, lean_object* v_a_244_, lean_object* v_b_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(v_s_239_, v___x_240_, v___x_241_, v_inst_242_, v_R_243_, v_a_244_, v_b_245_);
lean_dec_ref(v___x_240_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_instToFormatRaw___lam__0(lean_object* v_p_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = l_Nat_reprFast(v_p_247_);
v___x_249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Format_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Format_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Format_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Format_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Format_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
