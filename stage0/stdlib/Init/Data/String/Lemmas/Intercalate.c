// Lean compiler output
// Module: Init.Data.String.Lemmas.Intercalate
// Imports: public import Init.Data.String.Defs import all Init.Data.String.Defs public import Init.Data.String.Slice import all Init.Data.String.Slice import Init.ByCases
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_2_);
v_head_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref(v_x_1_);
v___x_8_ = lean_apply_2(v_h__2_3_, v_head_6_, v_tail_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter(lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__1_11_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_head_15_; lean_object* v_tail_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_11_);
v_head_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_head_15_);
v_tail_16_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_tail_16_);
lean_dec_ref(v_x_10_);
v___x_17_ = lean_apply_2(v_h__2_12_, v_head_15_, v_tail_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__2_20_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_head_23_; lean_object* v_tail_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_20_);
v_head_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_head_23_);
v_tail_24_ = lean_ctor_get(v_x_18_, 1);
lean_inc(v_tail_24_);
lean_dec_ref(v_x_18_);
v___x_25_ = lean_apply_2(v_h__1_19_, v_head_23_, v_tail_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter(lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_28_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_apply_1(v_h__2_29_, v___x_30_);
return v___x_31_;
}
else
{
lean_object* v_head_32_; lean_object* v_tail_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_29_);
v_head_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_head_32_);
v_tail_33_ = lean_ctor_get(v_x_27_, 1);
lean_inc(v_tail_33_);
lean_dec_ref(v_x_27_);
v___x_34_ = lean_apply_2(v_h__1_28_, v_head_32_, v_tail_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__2_37_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_37_);
v_head_40_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_head_40_);
v_tail_41_ = lean_ctor_get(v_x_35_, 1);
lean_inc(v_tail_41_);
lean_dec_ref(v_x_35_);
v___x_42_ = lean_apply_2(v_h__1_36_, v_head_40_, v_tail_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter(lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__2_46_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_46_);
v_head_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_head_49_);
v_tail_50_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_tail_50_);
lean_dec_ref(v_x_44_);
v___x_51_ = lean_apply_2(v_h__1_45_, v_head_49_, v_tail_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter___redArg(lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__1_53_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v_tail_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_53_);
v_head_57_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_head_57_);
v_tail_58_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_tail_58_);
lean_dec_ref(v_x_52_);
v___x_59_ = lean_apply_2(v_h__2_54_, v_head_57_, v_tail_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter(lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_63_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__1_62_, v___x_64_);
return v___x_65_;
}
else
{
lean_object* v_head_66_; lean_object* v_tail_67_; lean_object* v___x_68_; 
lean_dec(v_h__1_62_);
v_head_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_head_66_);
v_tail_67_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_tail_67_);
lean_dec_ref(v_x_61_);
v___x_68_ = lean_apply_2(v_h__2_63_, v_head_66_, v_tail_67_);
return v___x_68_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Intercalate(builtin);
}
#ifdef __cplusplus
}
#endif
