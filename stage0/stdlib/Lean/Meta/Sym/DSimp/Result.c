// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Result
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM
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
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_markAsDone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_markAsDone(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_4_; 
lean_dec_ref_known(v_x_3_, 0);
v___x_4_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0));
return v___x_4_;
}
else
{
lean_object* v_e_x27_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_13_; 
v_e_x27_5_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_13_ == 0)
{
v___x_7_ = v_x_3_;
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_e_x27_5_);
lean_dec(v_x_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
uint8_t v___x_9_; lean_object* v___x_11_; 
v___x_9_ = 1;
if (v_isShared_8_ == 0)
{
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_e_x27_5_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
lean_ctor_set_uint8(v___x_11_, sizeof(void*)*1, v___x_9_);
return v___x_11_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_inc_ref(v_x_14_);
return v_x_14_;
}
else
{
lean_object* v_e_x27_16_; 
v_e_x27_16_ = lean_ctor_get(v_x_15_, 0);
lean_inc_ref(v_e_x27_16_);
return v_e_x27_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_x_17_, v_x_18_);
lean_dec_ref(v_x_18_);
lean_dec_ref(v_x_17_);
return v_res_19_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Result(builtin);
}
#ifdef __cplusplus
}
#endif
