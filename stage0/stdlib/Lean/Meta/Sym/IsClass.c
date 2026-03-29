// Lean compiler output
// Module: Lean.Meta.Sym.IsClass
// Imports: public import Lean.Meta.Sym.SymM
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
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(lean_object* v_env_1_, lean_object* v_a_2_){
_start:
{
switch(lean_obj_tag(v_a_2_))
{
case 4:
{
lean_object* v_declName_3_; uint8_t v___x_4_; 
v_declName_3_ = lean_ctor_get(v_a_2_, 0);
lean_inc_n(v_declName_3_, 2);
lean_dec_ref(v_a_2_);
v___x_4_ = lean_is_class(v_env_1_, v_declName_3_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
lean_dec(v_declName_3_);
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_declName_3_);
return v___x_6_;
}
}
case 5:
{
lean_object* v_fn_7_; 
v_fn_7_ = lean_ctor_get(v_a_2_, 0);
lean_inc_ref(v_fn_7_);
lean_dec_ref(v_a_2_);
v_a_2_ = v_fn_7_;
goto _start;
}
case 7:
{
lean_object* v_body_9_; 
v_body_9_ = lean_ctor_get(v_a_2_, 2);
lean_inc_ref(v_body_9_);
lean_dec_ref(v_a_2_);
v_a_2_ = v_body_9_;
goto _start;
}
case 8:
{
lean_object* v_body_11_; 
v_body_11_ = lean_ctor_get(v_a_2_, 3);
lean_inc_ref(v_body_11_);
lean_dec_ref(v_a_2_);
v_a_2_ = v_body_11_;
goto _start;
}
case 10:
{
lean_object* v_expr_13_; 
v_expr_13_ = lean_ctor_get(v_a_2_, 1);
lean_inc_ref(v_expr_13_);
lean_dec_ref(v_a_2_);
v_a_2_ = v_expr_13_;
goto _start;
}
default: 
{
lean_object* v___x_15_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_env_1_);
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object* v_env_16_, lean_object* v_type_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(v_env_16_, v_type_17_);
return v___x_18_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_IsClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_IsClass(builtin);
}
#ifdef __cplusplus
}
#endif
