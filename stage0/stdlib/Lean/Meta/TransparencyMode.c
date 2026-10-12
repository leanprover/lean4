// Lean compiler output
// Module: Lean.Meta.TransparencyMode
// Imports: public import Init.Data.UInt.Basic public import Init.MetaTypes
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
LEAN_EXPORT uint64_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_TransparencyMode_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0 = (const lean_object*)&l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_TransparencyMode_instHashable__lean = (const lean_object*)&l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0_value;
static const lean_string_object l_Lean_Meta_TransparencyMode_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Meta_TransparencyMode_toString___closed__0 = (const lean_object*)&l_Lean_Meta_TransparencyMode_toString___closed__0_value;
static const lean_string_object l_Lean_Meta_TransparencyMode_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Meta_TransparencyMode_toString___closed__1 = (const lean_object*)&l_Lean_Meta_TransparencyMode_toString___closed__1_value;
static const lean_string_object l_Lean_Meta_TransparencyMode_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l_Lean_Meta_TransparencyMode_toString___closed__2 = (const lean_object*)&l_Lean_Meta_TransparencyMode_toString___closed__2_value;
static const lean_string_object l_Lean_Meta_TransparencyMode_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_TransparencyMode_toString___closed__3 = (const lean_object*)&l_Lean_Meta_TransparencyMode_toString___closed__3_value;
static const lean_string_object l_Lean_Meta_TransparencyMode_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Meta_TransparencyMode_toString___closed__4 = (const lean_object*)&l_Lean_Meta_TransparencyMode_toString___closed__4_value;
static const lean_string_object l_Lean_Meta_TransparencyMode_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l_Lean_Meta_TransparencyMode_toString___closed__5 = (const lean_object*)&l_Lean_Meta_TransparencyMode_toString___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toString___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_TransparencyMode_instToString__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_TransparencyMode_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_TransparencyMode_instToString__lean___closed__0 = (const lean_object*)&l_Lean_Meta_TransparencyMode_instToString__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_TransparencyMode_instToString__lean = (const lean_object*)&l_Lean_Meta_TransparencyMode_instToString__lean___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_hash(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
uint64_t v___x_2_; 
v___x_2_ = 7ULL;
return v___x_2_;
}
case 1:
{
uint64_t v___x_3_; 
v___x_3_ = 11ULL;
return v___x_3_;
}
case 2:
{
uint64_t v___x_4_; 
v___x_4_ = 13ULL;
return v___x_4_;
}
case 3:
{
uint64_t v___x_5_; 
v___x_5_ = 17ULL;
return v___x_5_;
}
case 4:
{
uint64_t v___x_6_; 
v___x_6_ = 19ULL;
return v___x_6_;
}
default: 
{
uint64_t v___x_7_; 
v___x_7_ = 23ULL;
return v___x_7_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
uint64_t v_res_8_;
v_res_8_ = l_Lean_Meta_TransparencyMode_hash(v_x_1_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_76__boxed_10_; uint64_t v_res_11_; lean_object* v_r_12_; 
v_x_76__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Lean_Meta_TransparencyMode_hash(v_x_76__boxed_10_);
v_r_12_ = lean_box_uint64(v_res_11_);
return v_r_12_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_toString(uint8_t v_x_21_){
_start:
{
switch(v_x_21_)
{
case 0:
{
lean_object* v___x_22_; 
v___x_22_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__0));
return v___x_22_;
}
case 1:
{
lean_object* v___x_23_; 
v___x_23_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__1));
return v___x_23_;
}
case 2:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__2));
return v___x_24_;
}
case 3:
{
lean_object* v___x_25_; 
v___x_25_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__3));
return v___x_25_;
}
case 4:
{
lean_object* v___x_26_; 
v___x_26_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__4));
return v___x_26_;
}
default: 
{
lean_object* v___x_27_; 
v___x_27_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__5));
return v___x_27_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_21_ = stack[0].m_num;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Meta_TransparencyMode_toString(v_x_21_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toString___boxed(lean_object* v_x_29_){
_start:
{
uint8_t v_x_58__boxed_30_; lean_object* v_res_31_; 
v_x_58__boxed_30_ = lean_unbox(v_x_29_);
v_res_31_ = l_Lean_Meta_TransparencyMode_toString(v_x_58__boxed_30_);
return v_res_31_;
}
}
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t v_x_34_, uint8_t v_x_35_){
_start:
{
switch(v_x_35_)
{
case 4:
{
uint8_t v___x_36_; 
v___x_36_ = 0;
return v___x_36_;
}
case 2:
{
if (v_x_34_ == 4)
{
uint8_t v___x_37_; 
v___x_37_ = 1;
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
}
case 3:
{
switch(v_x_34_)
{
case 4:
{
uint8_t v___x_39_; 
v___x_39_ = 1;
return v___x_39_;
}
case 2:
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
default: 
{
uint8_t v___x_41_; 
v___x_41_ = 0;
return v___x_41_;
}
}
}
case 5:
{
switch(v_x_34_)
{
case 4:
{
uint8_t v___x_42_; 
v___x_42_ = 1;
return v___x_42_;
}
case 2:
{
uint8_t v___x_43_; 
v___x_43_ = 1;
return v___x_43_;
}
case 3:
{
uint8_t v___x_44_; 
v___x_44_ = 1;
return v___x_44_;
}
default: 
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
}
}
case 0:
{
switch(v_x_34_)
{
case 4:
{
uint8_t v___x_46_; 
v___x_46_ = 1;
return v___x_46_;
}
case 2:
{
uint8_t v___x_47_; 
v___x_47_ = 1;
return v___x_47_;
}
case 3:
{
uint8_t v___x_48_; 
v___x_48_ = 1;
return v___x_48_;
}
case 5:
{
uint8_t v___x_49_; 
v___x_49_ = 1;
return v___x_49_;
}
case 1:
{
uint8_t v___x_50_; 
v___x_50_ = 1;
return v___x_50_;
}
default: 
{
uint8_t v___x_51_; 
v___x_51_ = 0;
return v___x_51_;
}
}
}
default: 
{
switch(v_x_34_)
{
case 4:
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
case 2:
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
case 3:
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
case 5:
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
default: 
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_lt_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_34_ = stack[0].m_num;
uint8_t v_x_35_ = stack[1].m_num;
uint8_t v_res_57_;
v_res_57_ = l_Lean_Meta_TransparencyMode_lt(v_x_34_, v_x_35_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_x_105__boxed_60_; uint8_t v_x_106__boxed_61_; uint8_t v_res_62_; lean_object* v_r_63_; 
v_x_105__boxed_60_ = lean_unbox(v_x_58_);
v_x_106__boxed_61_ = lean_unbox(v_x_59_);
v_res_62_ = l_Lean_Meta_TransparencyMode_lt(v_x_105__boxed_60_, v_x_106__boxed_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_TransparencyMode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_TransparencyMode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_TransparencyMode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_TransparencyMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_TransparencyMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_TransparencyMode(builtin);
}
#ifdef __cplusplus
}
#endif
