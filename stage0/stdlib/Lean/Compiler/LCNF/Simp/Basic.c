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
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_1_, v_fvarId_2_, v_a_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
if (lean_obj_tag(v_a_6_) == 1)
{
lean_dec_ref(v_a_6_);
lean_dec(v_fvarId_2_);
return v___x_5_;
}
else
{
lean_object* v___x_7_; 
lean_dec(v_a_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_1_, v_fvarId_2_, v_a_3_);
lean_dec(v_fvarId_2_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_24_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_24_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_24_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_24_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
if (lean_obj_tag(v_a_8_) == 1)
{
lean_object* v_val_17_; 
v_val_17_ = lean_ctor_get(v_a_8_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v_a_8_);
if (lean_obj_tag(v_val_17_) == 4)
{
lean_object* v_fvarId_18_; lean_object* v_args_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_fvarId_18_ = lean_ctor_get(v_val_17_, 0);
lean_inc(v_fvarId_18_);
v_args_19_ = lean_ctor_get(v_val_17_, 1);
lean_inc_ref(v_args_19_);
lean_dec_ref(v_val_17_);
v___x_20_ = lean_array_get_size(v_args_19_);
lean_dec_ref(v_args_19_);
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_nat_dec_eq(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_dec(v_fvarId_18_);
goto v___jp_12_;
}
else
{
lean_del_object(v___x_10_);
v_fvarId_2_ = v_fvarId_18_;
goto _start;
}
}
else
{
lean_dec(v_val_17_);
goto v___jp_12_;
}
}
else
{
lean_dec(v_a_8_);
goto v___jp_12_;
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_13_ = lean_box(0);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
v_a_25_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_7_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_7_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_2_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg___boxed(lean_object* v_pu_33_, lean_object* v_fvarId_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
uint8_t v_pu_boxed_37_; lean_object* v_res_38_; 
v_pu_boxed_37_ = lean_unbox(v_pu_33_);
v_res_38_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v_pu_boxed_37_, v_fvarId_34_, v_a_35_);
lean_dec(v_a_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(uint8_t v_pu_39_, lean_object* v_fvarId_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v_pu_39_, v_fvarId_40_, v_a_42_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___boxed(lean_object* v_pu_47_, lean_object* v_fvarId_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
uint8_t v_pu_boxed_54_; lean_object* v_res_55_; 
v_pu_boxed_54_ = lean_unbox(v_pu_47_);
v_res_55_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(v_pu_boxed_54_, v_fvarId_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
return v_res_55_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
