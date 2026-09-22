// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Basic
// Imports: public import Lean.Compiler.LCNF.CompilerM
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
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(uint8_t v_pu_1_, lean_object* v_fvarId_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_1_, v_fvarId_2_, v_a_3_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_a_9_);
if (lean_obj_tag(v_a_9_) == 1)
{
lean_dec_ref_known(v_a_9_, 1);
lean_dec(v_fvarId_2_);
return v___x_8_;
}
else
{
lean_object* v___x_10_; 
lean_dec(v_a_9_);
lean_dec_ref_known(v___x_8_, 1);
v___x_10_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_1_, v_fvarId_2_, v_a_3_);
lean_dec(v_fvarId_2_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_10_, 1);
if (lean_obj_tag(v_a_11_) == 1)
{
lean_object* v_val_12_; 
v_val_12_ = lean_ctor_get(v_a_11_, 0);
lean_inc(v_val_12_);
lean_dec_ref_known(v_a_11_, 1);
if (lean_obj_tag(v_val_12_) == 4)
{
lean_object* v_fvarId_13_; lean_object* v_args_14_; lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_fvarId_13_ = lean_ctor_get(v_val_12_, 0);
lean_inc(v_fvarId_13_);
v_args_14_ = lean_ctor_get(v_val_12_, 1);
lean_inc_ref(v_args_14_);
lean_dec_ref_known(v_val_12_, 2);
v___x_15_ = lean_array_get_size(v_args_14_);
lean_dec_ref(v_args_14_);
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_nat_dec_eq(v___x_15_, v___x_16_);
if (v___x_17_ == 0)
{
lean_dec(v_fvarId_13_);
goto v___jp_5_;
}
else
{
v_fvarId_2_ = v_fvarId_13_;
goto _start;
}
}
else
{
lean_dec(v_val_12_);
goto v___jp_5_;
}
}
else
{
lean_dec(v_a_11_);
goto v___jp_5_;
}
}
else
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
v_a_19_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___x_10_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_10_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_a_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_2_);
return v___x_8_;
}
v___jp_5_:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_box(0);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg___boxed(lean_object* v_pu_27_, lean_object* v_fvarId_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
uint8_t v_pu_boxed_31_; lean_object* v_res_32_; 
v_pu_boxed_31_ = lean_unbox(v_pu_27_);
v_res_32_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v_pu_boxed_31_, v_fvarId_28_, v_a_29_);
lean_dec(v_a_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(uint8_t v_pu_33_, lean_object* v_fvarId_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v_pu_33_, v_fvarId_34_, v_a_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___boxed(lean_object* v_pu_41_, lean_object* v_fvarId_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
uint8_t v_pu_boxed_48_; lean_object* v_res_49_; 
v_pu_boxed_48_ = lean_unbox(v_pu_41_);
v_res_49_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(v_pu_boxed_48_, v_fvarId_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_49_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
