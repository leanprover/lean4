// Lean compiler output
// Module: Init.Data.String.Stream
// Imports: public import Init.Data.String.Basic public import Init.Data.Stream
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instStreamRawChar___lam__0(lean_object*);
static const lean_closure_object l_instStreamRawChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instStreamRawChar___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instStreamRawChar___closed__0 = (const lean_object*)&l_instStreamRawChar___closed__0_value;
LEAN_EXPORT const lean_object* l_instStreamRawChar = (const lean_object*)&l_instStreamRawChar___closed__0_value;
LEAN_EXPORT lean_object* l_instStreamRawChar___lam__0(lean_object* v_s_1_){
_start:
{
lean_object* v_str_2_; lean_object* v_startPos_3_; lean_object* v_stopPos_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_20_; 
v_str_2_ = lean_ctor_get(v_s_1_, 0);
v_startPos_3_ = lean_ctor_get(v_s_1_, 1);
v_stopPos_4_ = lean_ctor_get(v_s_1_, 2);
v_isSharedCheck_20_ = !lean_is_exclusive(v_s_1_);
if (v_isSharedCheck_20_ == 0)
{
v___x_6_ = v_s_1_;
v_isShared_7_ = v_isSharedCheck_20_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_stopPos_4_);
lean_inc(v_startPos_3_);
lean_inc(v_str_2_);
lean_dec(v_s_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_20_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v_startPos_3_, v___x_8_);
v___x_10_ = lean_nat_dec_le(v___x_9_, v_stopPos_4_);
lean_dec(v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_del_object(v___x_6_);
lean_dec(v_stopPos_4_);
lean_dec(v_startPos_3_);
lean_dec_ref(v_str_2_);
v___x_11_ = lean_box(0);
return v___x_11_;
}
else
{
uint32_t v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_12_ = lean_string_utf8_get(v_str_2_, v_startPos_3_);
v___x_13_ = lean_string_utf8_next(v_str_2_, v_startPos_3_);
lean_dec(v_startPos_3_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_13_);
v___x_15_ = v___x_6_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_str_2_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_19_, 2, v_stopPos_4_);
v___x_15_ = v_reuseFailAlloc_19_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box_uint32(v___x_12_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___x_15_);
v___x_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
}
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Stream(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Stream(builtin);
}
#ifdef __cplusplus
}
#endif
