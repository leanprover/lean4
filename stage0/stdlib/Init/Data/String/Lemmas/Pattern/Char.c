// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Char
// Imports: public import Init.Data.String.Pattern.Char public import Init.Data.String.Lemmas.Pattern.Basic public import Init.Data.String.Slice public import Init.Data.String.Lemmas.Pattern.Pred public import Init.Data.String.Search import all Init.Data.String.Slice import all Init.Data.String.Pattern.Char import all Init.Data.String.Search import Init.Data.Option.Lemmas import Init.Data.String.Lemmas.Basic import Init.Data.String.Lemmas.Order import Init.Data.Order.Lemmas import Init.Data.String.OrderInstances import Init.Omega import Init.Data.String.Lemmas.FindPos
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_String_Slice_Pattern_Model_Char_instPatternModelChar___redArg();
return v_res_5_;
}
}
lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar(uint32_t v_c_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Model_Char_instPatternModelChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_6_ = stack[0].m_num;
lean_object* v_res_8_;
v_res_8_ = l_String_Slice_Pattern_Model_Char_instPatternModelChar(v_c_6_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_Char_instPatternModelChar___boxed(lean_object* v_c_9_){
_start:
{
uint32_t v_c_boxed_10_; lean_object* v_res_11_; 
v_c_boxed_10_ = lean_unbox_uint32(v_c_9_);
lean_dec(v_c_9_);
v_res_11_ = l_String_Slice_Pattern_Model_Char_instPatternModelChar(v_c_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_13_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_apply_1(v_h__2_14_, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v_val_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_14_);
v_val_17_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_x_12_, 1);
v___x_18_ = lean_apply_1(v_h__1_13_, v_val_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_19_, lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__2_23_, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_23_);
v_val_26_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v_x_21_, 1);
v___x_27_ = lean_apply_1(v_h__1_22_, v_val_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_28_, v_motive_29_, v_x_30_, v_h__1_31_, v_h__2_32_);
lean_dec_ref(v_s_28_);
return v_res_33_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Char(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_Char(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_Char(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Pred(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_Char(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
}
#ifdef __cplusplus
}
#endif
