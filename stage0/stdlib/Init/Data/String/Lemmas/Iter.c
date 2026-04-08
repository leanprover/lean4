// Lean compiler output
// Module: Init.Data.String.Lemmas.Iter
// Imports: public import Init.Data.String.Iter.Intercalate public import Init.Data.String.Slice import all Init.Data.String.Iter.Intercalate import all Init.Data.String.Defs import Init.Data.String.Lemmas.Intercalate import Init.Data.Iterators.Lemmas.Consumers.Loop import Init.Data.Iterators.Lemmas.Combinators.FilterMap
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_2(v_h__2_4_, v_val_6_, v_x_2_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter(lean_object* v_motive_8_, lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v___x_13_; 
lean_dec(v_h__2_12_);
v___x_13_ = lean_apply_1(v_h__1_11_, v_x_10_);
return v___x_13_;
}
else
{
lean_object* v_val_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_11_);
v_val_14_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_val_14_);
lean_dec_ref(v_x_9_);
v___x_15_ = lean_apply_2(v_h__2_12_, v_val_14_, v_x_10_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter___redArg(lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v___x_20_; 
lean_dec(v_h__2_19_);
v___x_20_ = lean_apply_1(v_h__1_18_, v_x_17_);
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_18_);
v_val_21_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_val_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_2(v_h__2_19_, v_val_21_, v_x_17_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter(lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_28_; 
lean_dec(v_h__2_27_);
v___x_28_ = lean_apply_1(v_h__1_26_, v_x_25_);
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_30_; 
lean_dec(v_h__1_26_);
v_val_29_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_val_29_);
lean_dec_ref(v_x_24_);
v___x_30_ = lean_apply_2(v_h__2_27_, v_val_29_, v_x_25_);
return v___x_30_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Iter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Iter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Iter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Iter_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iter_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Iter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Iter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Iter(builtin);
}
#ifdef __cplusplus
}
#endif
