// Lean compiler output
// Module: Init.Data.ToString.Extra
// Imports: public import Init.Data.String.Defs public import Init.Data.Int.Repr
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_instToStringUInt8___lam__0___boxed(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static const lean_string_object l_List_toString___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_toString___redArg___lam__0___closed__0 = (const lean_object*)&l_List_toString___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_toString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_toString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___redArg___closed__0 = (const lean_object*)&l_List_toString___redArg___closed__0_value;
static const lean_string_object l_List_toString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___redArg___closed__1 = (const lean_object*)&l_List_toString___redArg___closed__1_value;
static const lean_string_object l_List_toString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___redArg___closed__2 = (const lean_object*)&l_List_toString___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringList(lean_object*, lean_object*);
static const lean_string_object l_instToStringArray___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_instToStringArray___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringArray___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringByteArray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringByteArray___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instToStringByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringByteArray___closed__0 = (const lean_object*)&l_instToStringByteArray___closed__0_value;
static const lean_closure_object l_instToStringByteArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringByteArray___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_instToStringByteArray___closed__0_value)} };
static const lean_object* l_instToStringByteArray___closed__1 = (const lean_object*)&l_instToStringByteArray___closed__1_value;
LEAN_EXPORT const lean_object* l_instToStringByteArray = (const lean_object*)&l_instToStringByteArray___closed__1_value;
static const lean_closure_object l_instToStringInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt___closed__0 = (const lean_object*)&l_instToStringInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt = (const lean_object*)&l_instToStringInt___closed__0_value;
LEAN_EXPORT lean_object* l_List_toString___redArg___lam__0(lean_object* v_inst_2_, lean_object* v_l_3_, lean_object* v_r_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = ((lean_object*)(l_List_toString___redArg___lam__0___closed__0));
v___x_6_ = lean_string_append(v_l_3_, v___x_5_);
v___x_7_ = lean_apply_1(v_inst_2_, v_r_4_);
v___x_8_ = lean_string_append(v___x_6_, v___x_7_);
lean_dec_ref(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_List_toString___redArg(lean_object* v_inst_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_object* v___x_14_; 
lean_dec_ref(v_inst_12_);
v___x_14_ = ((lean_object*)(l_List_toString___redArg___closed__0));
return v___x_14_;
}
else
{
lean_object* v_tail_15_; 
v_tail_15_ = lean_ctor_get(v_x_13_, 1);
if (lean_obj_tag(v_tail_15_) == 0)
{
lean_object* v_head_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_head_16_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_head_16_);
lean_dec_ref(v_x_13_);
v___x_17_ = ((lean_object*)(l_List_toString___redArg___closed__1));
v___x_18_ = lean_apply_1(v_inst_12_, v_head_16_);
v___x_19_ = lean_string_append(v___x_17_, v___x_18_);
lean_dec_ref(v___x_18_);
v___x_20_ = ((lean_object*)(l_List_toString___redArg___closed__2));
v___x_21_ = lean_string_append(v___x_19_, v___x_20_);
return v___x_21_;
}
else
{
lean_object* v_head_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint32_t v___x_28_; lean_object* v___x_29_; 
lean_inc(v_tail_15_);
v_head_22_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_head_22_);
lean_dec_ref(v_x_13_);
lean_inc_ref(v_inst_12_);
v___f_23_ = lean_alloc_closure((void*)(l_List_toString___redArg___lam__0), 3, 1);
lean_closure_set(v___f_23_, 0, v_inst_12_);
v___x_24_ = ((lean_object*)(l_List_toString___redArg___closed__1));
v___x_25_ = lean_apply_1(v_inst_12_, v_head_22_);
v___x_26_ = lean_string_append(v___x_24_, v___x_25_);
lean_dec_ref(v___x_25_);
v___x_27_ = l_List_foldl___redArg(v___f_23_, v___x_26_, v_tail_15_);
v___x_28_ = 93;
v___x_29_ = lean_string_push(v___x_27_, v___x_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_List_toString___redArg(v_inst_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_instToStringList___redArg(lean_object* v_inst_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_closure((void*)(l_List_toString), 3, 2);
lean_closure_set(v___x_35_, 0, lean_box(0));
lean_closure_set(v___x_35_, 1, v_inst_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_instToStringList(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_closure((void*)(l_List_toString), 3, 2);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, v_inst_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_instToStringArray___redArg___lam__0(lean_object* v_inst_40_, lean_object* v_xs_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_42_ = ((lean_object*)(l_instToStringArray___redArg___lam__0___closed__0));
v___x_43_ = lean_array_to_list(v_xs_41_);
v___x_44_ = l_List_toString___redArg(v_inst_40_, v___x_43_);
v___x_45_ = lean_string_append(v___x_42_, v___x_44_);
lean_dec_ref(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_instToStringArray___redArg(lean_object* v_inst_46_){
_start:
{
lean_object* v___f_47_; 
v___f_47_ = lean_alloc_closure((void*)(l_instToStringArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_47_, 0, v_inst_46_);
return v___f_47_;
}
}
LEAN_EXPORT lean_object* l_instToStringArray(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___f_50_; 
v___f_50_ = lean_alloc_closure((void*)(l_instToStringArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_50_, 0, v_inst_49_);
return v___f_50_;
}
}
LEAN_EXPORT lean_object* l_instToStringByteArray___lam__0(lean_object* v___f_51_, lean_object* v_bs_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = l_ByteArray_toList(v_bs_52_);
v___x_54_ = l_List_toString___redArg(v___f_51_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_instToStringByteArray___lam__0___boxed(lean_object* v___f_55_, lean_object* v_bs_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_instToStringByteArray___lam__0(v___f_55_, v_bs_56_);
lean_dec_ref(v_bs_56_);
return v_res_57_;
}
}
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ToString_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ToString_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
