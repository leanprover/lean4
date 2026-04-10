// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadVar
// Imports: public import Lean.Meta.Sym.Arith.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_inst_1_, v_x_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg(lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_8_, 0, v_inst_7_);
lean_closure_set(v___f_8_, 1, v_inst_6_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift(lean_object* v_m_9_, lean_object* v_n_10_, lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v_inst_12_);
lean_closure_set(v___f_13_, 1, v_inst_11_);
return v___f_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_e_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_apply_1(v_inst_14_, v_e_16_);
v___x_18_ = lean_apply_2(v_inst_15_, lean_box(0), v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_21_, 0, v_inst_20_);
lean_closure_set(v___f_21_, 1, v_inst_19_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift(lean_object* v_m_22_, lean_object* v_n_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_26_, 0, v_inst_25_);
lean_closure_set(v___f_26_, 1, v_inst_24_);
return v___f_26_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
}
#ifdef __cplusplus
}
#endif
