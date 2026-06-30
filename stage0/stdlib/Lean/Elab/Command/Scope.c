// Lean compiler output
// Module: Lean.Elab.Command.Scope
// Imports: public import Lean.Parser.Term
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
extern lean_object* l_Lean_Options_empty;
static const lean_string_object l_Lean_Elab_Command_instInhabitedScope_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Command_instInhabitedScope_default___closed__0 = (const lean_object*)&l_Lean_Elab_Command_instInhabitedScope_default___closed__0_value;
static const lean_array_object l_Lean_Elab_Command_instInhabitedScope_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_instInhabitedScope_default___closed__1 = (const lean_object*)&l_Lean_Elab_Command_instInhabitedScope_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Command_instInhabitedScope_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_instInhabitedScope_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedScope;
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__2(void){
_start:
{
uint8_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_4_ = 0;
v___x_5_ = ((lean_object*)(l_Lean_Elab_Command_instInhabitedScope_default___closed__1));
v___x_6_ = lean_box(0);
v___x_7_ = lean_box(0);
v___x_8_ = l_Lean_Options_empty;
v___x_9_ = ((lean_object*)(l_Lean_Elab_Command_instInhabitedScope_default___closed__0));
v___x_10_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
lean_ctor_set(v___x_10_, 3, v___x_6_);
lean_ctor_set(v___x_10_, 4, v___x_6_);
lean_ctor_set(v___x_10_, 5, v___x_5_);
lean_ctor_set(v___x_10_, 6, v___x_5_);
lean_ctor_set(v___x_10_, 7, v___x_6_);
lean_ctor_set(v___x_10_, 8, v___x_6_);
lean_ctor_set(v___x_10_, 9, v___x_6_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*10, v___x_4_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*10 + 1, v___x_4_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*10 + 2, v___x_4_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Elab_Command_instInhabitedScope_default___closed__2, &l_Lean_Elab_Command_instInhabitedScope_default___closed__2_once, _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__2);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Elab_Command_instInhabitedScope_default;
return v___x_12_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Command_Scope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_instInhabitedScope_default = _init_l_Lean_Elab_Command_instInhabitedScope_default();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope_default);
l_Lean_Elab_Command_instInhabitedScope = _init_l_Lean_Elab_Command_instInhabitedScope();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Command_Scope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Command_Scope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command_Scope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Command_Scope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Command_Scope(builtin);
}
#ifdef __cplusplus
}
#endif
