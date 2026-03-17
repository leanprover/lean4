// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Nat public import Lean.Meta.Tactic.Simp.Arith.Int
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
uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object*);
uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object*);
uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_parentIsTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_parentIsTarget___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_parentIsTarget(lean_object* v_parent_x3f_1_){
_start:
{
if (lean_obj_tag(v_parent_x3f_1_) == 0)
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
else
{
lean_object* v_val_3_; uint8_t v___y_5_; uint8_t v___x_7_; 
v_val_3_ = lean_ctor_get(v_parent_x3f_1_, 0);
lean_inc(v_val_3_);
lean_dec_ref(v_parent_x3f_1_);
lean_inc(v_val_3_);
v___x_7_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_val_3_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
lean_inc(v_val_3_);
v___x_8_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_val_3_);
v___y_5_ = v___x_8_;
goto v___jp_4_;
}
else
{
v___y_5_ = v___x_7_;
goto v___jp_4_;
}
v___jp_4_:
{
if (v___y_5_ == 0)
{
uint8_t v___x_6_; 
v___x_6_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_val_3_);
return v___x_6_;
}
else
{
lean_dec(v_val_3_);
return v___y_5_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_parentIsTarget___boxed(lean_object* v_parent_x3f_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Lean_Meta_Simp_Arith_parentIsTarget(v_parent_x3f_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
}
#ifdef __cplusplus
}
#endif
