// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound
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
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instFormulaPosFinDefaultClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instFormulaPosFinDefaultClause(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc(v_n_1_);
v___x_2_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed), 2, 1);
lean_closure_set(v___x_2_, 0, v_n_1_);
lean_inc(v_n_1_);
v___x_3_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray), 2, 1);
lean_closure_set(v___x_3_, 0, v_n_1_);
lean_inc(v_n_1_);
v___x_4_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed), 3, 1);
lean_closure_set(v___x_4_, 0, v_n_1_);
lean_inc(v_n_1_);
v___x_5_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed), 3, 1);
lean_closure_set(v___x_5_, 0, v_n_1_);
lean_inc(v_n_1_);
v___x_6_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed), 4, 1);
lean_closure_set(v___x_6_, 0, v_n_1_);
v___x_7_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed), 6, 1);
lean_closure_set(v___x_7_, 0, v_n_1_);
v___x_8_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_8_, 0, v___x_2_);
lean_ctor_set(v___x_8_, 1, v___x_3_);
lean_ctor_set(v___x_8_, 2, v___x_4_);
lean_ctor_set(v___x_8_, 3, v___x_5_);
lean_ctor_set(v___x_8_, 4, v___x_6_);
lean_ctor_set(v___x_8_, 5, v___x_7_);
return v___x_8_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
}
#ifdef __cplusplus
}
#endif
