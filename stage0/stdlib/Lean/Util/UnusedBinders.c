// Lean compiler output
// Module: Lean.Util.UnusedBinders
// Imports: public import Lean.Expr
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere(lean_object* v_p_1_, lean_object* v_e_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_Expr_cleanupAnnotations(v_e_2_);
switch(lean_obj_tag(v___x_3_))
{
case 7:
{
lean_object* v_binderType_4_; lean_object* v_body_5_; uint8_t v_binderInfo_6_; lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_binderType_4_ = lean_ctor_get(v___x_3_, 1);
lean_inc_ref(v_binderType_4_);
v_body_5_ = lean_ctor_get(v___x_3_, 2);
lean_inc_ref(v_body_5_);
v_binderInfo_6_ = lean_ctor_get_uint8(v___x_3_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3_, 3);
v___x_7_ = lean_box(v_binderInfo_6_);
lean_inc_ref(v_p_1_);
v___x_8_ = lean_apply_2(v_p_1_, v___x_7_, v_binderType_4_);
v___x_9_ = lean_unbox(v___x_8_);
if (v___x_9_ == 0)
{
v_e_2_ = v_body_5_;
goto _start;
}
else
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_expr_has_loose_bvar(v_body_5_, v___x_11_);
if (v___x_12_ == 0)
{
uint8_t v___x_13_; 
lean_dec_ref(v_body_5_);
lean_dec_ref(v_p_1_);
v___x_13_ = lean_unbox(v___x_8_);
return v___x_13_;
}
else
{
v_e_2_ = v_body_5_;
goto _start;
}
}
}
case 8:
{
lean_object* v_body_15_; 
v_body_15_ = lean_ctor_get(v___x_3_, 3);
lean_inc_ref(v_body_15_);
lean_dec_ref_known(v___x_3_, 4);
v_e_2_ = v_body_15_;
goto _start;
}
default: 
{
uint8_t v___x_17_; 
lean_dec_ref(v___x_3_);
lean_dec_ref(v_p_1_);
v___x_17_ = 0;
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___boxed(lean_object* v_p_18_, lean_object* v_e_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Lean_Expr_hasUnusedForallBindersWhere(v_p_18_, v_e_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_UnusedBinders(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_UnusedBinders(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_UnusedBinders(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_UnusedBinders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_UnusedBinders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_UnusedBinders(builtin);
}
#ifdef __cplusplus
}
#endif
