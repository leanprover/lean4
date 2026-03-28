// Lean compiler output
// Module: Init.Data.Option.BasicAux
// Imports: public import Init.Util
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
static const lean_string_object l_Option_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Option_get_x21___redArg___closed__0 = (const lean_object*)&l_Option_get_x21___redArg___closed__0_value;
static const lean_string_object l_Option_get_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Option_get_x21___redArg___closed__1 = (const lean_object*)&l_Option_get_x21___redArg___closed__1_value;
static const lean_string_object l_Option_get_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Option_get_x21___redArg___closed__2 = (const lean_object*)&l_Option_get_x21___redArg___closed__2_value;
static lean_once_cell_t l_Option_get_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Option_get_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Option_get_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Option_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((lean_object*)(l_Option_get_x21___redArg___closed__2));
v___x_5_ = lean_unsigned_to_nat(14u);
v___x_6_ = lean_unsigned_to_nat(22u);
v___x_7_ = ((lean_object*)(l_Option_get_x21___redArg___closed__1));
v___x_8_ = ((lean_object*)(l_Option_get_x21___redArg___closed__0));
v___x_9_ = l_mkPanicMessageWithDecl(v___x_8_, v___x_7_, v___x_6_, v___x_5_, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___redArg(lean_object* v_inst_10_, lean_object* v_x_11_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_obj_once(&l_Option_get_x21___redArg___closed__3, &l_Option_get_x21___redArg___closed__3_once, _init_l_Option_get_x21___redArg___closed__3);
v___x_13_ = l_panic___redArg(v_inst_10_, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v_val_14_; 
v_val_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_14_);
return v_val_14_;
}
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___redArg___boxed(lean_object* v_inst_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Option_get_x21___redArg(v_inst_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec(v_inst_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Option_get_x21(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Option_get_x21___redArg___closed__3, &l_Option_get_x21___redArg___closed__3_once, _init_l_Option_get_x21___redArg___closed__3);
v___x_22_ = l_panic___redArg(v_inst_19_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_val_23_; 
v_val_23_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_val_23_);
return v_val_23_;
}
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___boxed(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Option_get_x21(v_00_u03b1_24_, v_inst_25_, v_x_26_);
lean_dec(v_x_26_);
lean_dec(v_inst_25_);
return v_res_27_;
}
}
lean_object* runtime_initialize_Init_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_BasicAux(builtin);
}
#ifdef __cplusplus
}
#endif
