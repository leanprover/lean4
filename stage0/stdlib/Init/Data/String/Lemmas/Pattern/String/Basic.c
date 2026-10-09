// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.String.Basic
// Imports: public import Init.Data.String.Pattern.String public import Init.Data.String.Lemmas.Pattern.Basic import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Lemmas.Basic import Init.Data.String.Lemmas.Intercalate import Init.Data.String.OrderInstances import Init.Data.String.Lemmas.Splits import Init.Data.ByteArray.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel(lean_object* v_pat_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel___boxed(lean_object* v_pat_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_String_Slice_Pattern_Model_ForwardSliceSearcher_instPatternModel(v_pat_8_);
lean_dec_ref(v_pat_8_);
return v_res_9_;
}
}
lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_12_;
v_res_12_ = l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg();
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel(lean_object* v_pat_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel___boxed(lean_object* v_pat_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_String_Slice_Pattern_Model_ForwardStringSearcher_instPatternModel(v_pat_17_);
lean_dec_ref(v_pat_17_);
return v_res_18_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Intercalate(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
