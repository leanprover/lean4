// Lean compiler output
// Module: Std.Sat.CNF.Unit
// Imports: public import Std.Sat.CNF.Basic public import Std.Sat.CNF.Sat public import Std.Sat.CNF.Relabel public import Std.Sat.CNF.Entails import Init.ByCases
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
static const lean_array_object l_Std_Sat_CNF_Clause_unit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_CNF_Clause_unit___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_Clause_unit___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit___redArg(lean_object* v_atom_3_, uint8_t v_pol_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___y_9_; 
v___x_5_ = ((lean_object*)(l_Std_Sat_CNF_Clause_unit___redArg___closed__0));
v___x_6_ = l_ByteArray_empty;
v___x_7_ = lean_array_push(v___x_5_, v_atom_3_);
if (v_pol_4_ == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 0;
v___y_9_ = v___x_12_;
goto v___jp_8_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 1;
v___y_9_ = v___x_13_;
goto v___jp_8_;
}
v___jp_8_:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_byte_array_push(v___x_6_, v___y_9_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_7_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit___redArg___boxed(lean_object* v_atom_14_, lean_object* v_pol_15_){
_start:
{
uint8_t v_pol_boxed_16_; lean_object* v_res_17_; 
v_pol_boxed_16_ = lean_unbox(v_pol_15_);
v_res_17_ = l_Std_Sat_CNF_Clause_unit___redArg(v_atom_14_, v_pol_boxed_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit(lean_object* v_00_u03b1_18_, lean_object* v_atom_19_, uint8_t v_pol_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Std_Sat_CNF_Clause_unit___redArg(v_atom_19_, v_pol_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_unit___boxed(lean_object* v_00_u03b1_22_, lean_object* v_atom_23_, lean_object* v_pol_24_){
_start:
{
uint8_t v_pol_boxed_25_; lean_object* v_res_26_; 
v_pol_boxed_25_ = lean_unbox(v_pol_24_);
v_res_26_ = l_Std_Sat_CNF_Clause_unit(v_00_u03b1_22_, v_atom_23_, v_pol_boxed_25_);
return v_res_26_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Sat(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Unit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Unit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Sat(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Unit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Unit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Unit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Unit(builtin);
}
#ifdef __cplusplus
}
#endif
