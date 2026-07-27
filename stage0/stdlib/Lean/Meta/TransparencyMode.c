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
LEAN_EXPORT uint64_t l_Lean_Meta_TransparencyMode_hash(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_x_76__boxed_9_; uint64_t v_res_10_; lean_object* v_r_11_; 
v_x_76__boxed_9_ = lean_unbox(v_x_8_);
v_res_10_ = l_Lean_Meta_TransparencyMode_hash(v_x_76__boxed_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toString(uint8_t v_x_20_){
_start:
{
switch(v_x_20_)
{
case 0:
{
lean_object* v___x_21_; 
v___x_21_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__0));
return v___x_21_;
}
case 1:
{
lean_object* v___x_22_; 
v___x_22_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__1));
return v___x_22_;
}
case 2:
{
lean_object* v___x_23_; 
v___x_23_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__2));
return v___x_23_;
}
case 3:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__3));
return v___x_24_;
}
case 4:
{
lean_object* v___x_25_; 
v___x_25_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__4));
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; 
v___x_26_ = ((lean_object*)(l_Lean_Meta_TransparencyMode_toString___closed__5));
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toString___boxed(lean_object* v_x_27_){
_start:
{
uint8_t v_x_58__boxed_28_; lean_object* v_res_29_; 
v_x_58__boxed_28_ = lean_unbox(v_x_27_);
v_res_29_ = l_Lean_Meta_TransparencyMode_toString(v_x_58__boxed_28_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t v_x_32_, uint8_t v_x_33_){
_start:
{
switch(v_x_33_)
{
case 4:
{
uint8_t v___x_34_; 
v___x_34_ = 0;
return v___x_34_;
}
case 2:
{
switch(v_x_32_)
{
case 4:
{
uint8_t v___x_35_; 
v___x_35_ = 1;
return v___x_35_;
}
case 2:
{
uint8_t v___x_36_; 
v___x_36_ = 0;
return v___x_36_;
}
case 3:
{
uint8_t v___x_37_; 
v___x_37_ = 0;
return v___x_37_;
}
case 5:
{
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
default: 
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
}
case 3:
{
switch(v_x_32_)
{
case 4:
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
case 2:
{
uint8_t v___x_41_; 
v___x_41_ = 1;
return v___x_41_;
}
case 3:
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
case 5:
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
default: 
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
}
case 5:
{
switch(v_x_32_)
{
case 4:
{
uint8_t v___x_45_; 
v___x_45_ = 1;
return v___x_45_;
}
case 2:
{
uint8_t v___x_46_; 
v___x_46_ = 1;
return v___x_46_;
}
case 3:
{
uint8_t v___x_47_; 
v___x_47_ = 1;
return v___x_47_;
}
case 5:
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
default: 
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
}
case 0:
{
switch(v_x_32_)
{
case 4:
{
uint8_t v___x_50_; 
v___x_50_ = 1;
return v___x_50_;
}
case 2:
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
case 3:
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
case 5:
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
case 1:
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
default: 
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
}
}
default: 
{
switch(v_x_32_)
{
case 4:
{
uint8_t v___x_56_; 
v___x_56_ = 1;
return v___x_56_;
}
case 2:
{
uint8_t v___x_57_; 
v___x_57_ = 1;
return v___x_57_;
}
case 3:
{
uint8_t v___x_58_; 
v___x_58_ = 1;
return v___x_58_;
}
case 5:
{
uint8_t v___x_59_; 
v___x_59_ = 1;
return v___x_59_;
}
default: 
{
uint8_t v___x_60_; 
v___x_60_ = 0;
return v___x_60_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_x_137__boxed_63_; uint8_t v_x_138__boxed_64_; uint8_t v_res_65_; lean_object* v_r_66_; 
v_x_137__boxed_63_ = lean_unbox(v_x_61_);
v_x_138__boxed_64_ = lean_unbox(v_x_62_);
v_res_65_ = l_Lean_Meta_TransparencyMode_lt(v_x_137__boxed_63_, v_x_138__boxed_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_TransparencyMode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
