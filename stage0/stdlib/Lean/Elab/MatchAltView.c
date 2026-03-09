// Lean compiler output
// Module: Lean.Elab.MatchAltView
// Imports: public import Lean.Elab.Term
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
static const lean_array_object l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1 = (const lean_object*)&l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView_default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_instInhabitedMatchAltView_default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_instInhabitedMatchAltView_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_instInhabitedMatchAltView(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MatchAltView(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_MatchAltView(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MatchAltView(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_MatchAltView(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_MatchAltView(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_MatchAltView(builtin);
}
#ifdef __cplusplus
}
#endif
