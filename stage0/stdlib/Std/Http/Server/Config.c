// Lean compiler output
// Module: Std.Http.Server.Config
// Imports: public import Std.Time public import Std.Http.Protocol.H1
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
LEAN_EXPORT lean_object* l_Std_Http_Config_toH1Config(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Config_toH1Config___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Config_toH1Config(lean_object* v_config_1_){
_start:
{
lean_object* v_maxRequests_2_; lean_object* v_maxHeaders_3_; lean_object* v_maxHeaderBytes_4_; uint8_t v_enableKeepAlive_5_; lean_object* v_serverName_6_; lean_object* v_maxUriLength_7_; lean_object* v_maxStartLineLength_8_; lean_object* v_maxHeaderNameLength_9_; lean_object* v_maxHeaderValueLength_10_; lean_object* v_maxSpaceSequence_11_; lean_object* v_maxLeadingEmptyLines_12_; lean_object* v_maxChunkExtNameLength_13_; lean_object* v_maxChunkExtValueLength_14_; lean_object* v_maxChunkLineLength_15_; lean_object* v_maxChunkSize_16_; lean_object* v_maxBodySize_17_; lean_object* v_maxReasonPhraseLength_18_; lean_object* v_maxTrailerHeaders_19_; lean_object* v_maxChunkExtensions_20_; lean_object* v___x_21_; 
v_maxRequests_2_ = lean_ctor_get(v_config_1_, 1);
v_maxHeaders_3_ = lean_ctor_get(v_config_1_, 2);
v_maxHeaderBytes_4_ = lean_ctor_get(v_config_1_, 3);
v_enableKeepAlive_5_ = lean_ctor_get_uint8(v_config_1_, sizeof(void*)*24);
v_serverName_6_ = lean_ctor_get(v_config_1_, 9);
v_maxUriLength_7_ = lean_ctor_get(v_config_1_, 10);
v_maxStartLineLength_8_ = lean_ctor_get(v_config_1_, 11);
v_maxHeaderNameLength_9_ = lean_ctor_get(v_config_1_, 12);
v_maxHeaderValueLength_10_ = lean_ctor_get(v_config_1_, 13);
v_maxSpaceSequence_11_ = lean_ctor_get(v_config_1_, 14);
v_maxLeadingEmptyLines_12_ = lean_ctor_get(v_config_1_, 15);
v_maxChunkExtNameLength_13_ = lean_ctor_get(v_config_1_, 16);
v_maxChunkExtValueLength_14_ = lean_ctor_get(v_config_1_, 17);
v_maxChunkLineLength_15_ = lean_ctor_get(v_config_1_, 18);
v_maxChunkSize_16_ = lean_ctor_get(v_config_1_, 19);
v_maxBodySize_17_ = lean_ctor_get(v_config_1_, 20);
v_maxReasonPhraseLength_18_ = lean_ctor_get(v_config_1_, 21);
v_maxTrailerHeaders_19_ = lean_ctor_get(v_config_1_, 22);
v_maxChunkExtensions_20_ = lean_ctor_get(v_config_1_, 23);
lean_inc(v_maxTrailerHeaders_19_);
lean_inc(v_maxReasonPhraseLength_18_);
lean_inc(v_maxBodySize_17_);
lean_inc(v_maxChunkSize_16_);
lean_inc(v_maxChunkLineLength_15_);
lean_inc(v_maxChunkExtValueLength_14_);
lean_inc(v_maxChunkExtNameLength_13_);
lean_inc(v_maxChunkExtensions_20_);
lean_inc(v_maxLeadingEmptyLines_12_);
lean_inc(v_maxSpaceSequence_11_);
lean_inc(v_maxHeaderValueLength_10_);
lean_inc(v_maxHeaderNameLength_9_);
lean_inc(v_maxStartLineLength_8_);
lean_inc(v_maxUriLength_7_);
lean_inc(v_serverName_6_);
lean_inc(v_maxHeaderBytes_4_);
lean_inc(v_maxHeaders_3_);
lean_inc(v_maxRequests_2_);
v___x_21_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v___x_21_, 0, v_maxRequests_2_);
lean_ctor_set(v___x_21_, 1, v_maxHeaders_3_);
lean_ctor_set(v___x_21_, 2, v_maxHeaderBytes_4_);
lean_ctor_set(v___x_21_, 3, v_serverName_6_);
lean_ctor_set(v___x_21_, 4, v_maxUriLength_7_);
lean_ctor_set(v___x_21_, 5, v_maxStartLineLength_8_);
lean_ctor_set(v___x_21_, 6, v_maxHeaderNameLength_9_);
lean_ctor_set(v___x_21_, 7, v_maxHeaderValueLength_10_);
lean_ctor_set(v___x_21_, 8, v_maxSpaceSequence_11_);
lean_ctor_set(v___x_21_, 9, v_maxLeadingEmptyLines_12_);
lean_ctor_set(v___x_21_, 10, v_maxChunkExtensions_20_);
lean_ctor_set(v___x_21_, 11, v_maxChunkExtNameLength_13_);
lean_ctor_set(v___x_21_, 12, v_maxChunkExtValueLength_14_);
lean_ctor_set(v___x_21_, 13, v_maxChunkLineLength_15_);
lean_ctor_set(v___x_21_, 14, v_maxChunkSize_16_);
lean_ctor_set(v___x_21_, 15, v_maxBodySize_17_);
lean_ctor_set(v___x_21_, 16, v_maxReasonPhraseLength_18_);
lean_ctor_set(v___x_21_, 17, v_maxTrailerHeaders_19_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*18, v_enableKeepAlive_5_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Config_toH1Config___boxed(lean_object* v_config_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_Http_Config_toH1Config(v_config_22_);
lean_dec_ref(v_config_22_);
return v_res_23_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Server_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Server_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Server_Config(builtin);
}
#ifdef __cplusplus
}
#endif
