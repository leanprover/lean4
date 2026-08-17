// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.BVDecide.Types
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.DSimp.DSimpM public import Lean.Meta.Sym.Simp.SimpM
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_bvExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(lean_object* v___x_1_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed(lean_object* v___x_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(v___x_4_);
return v_res_6_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_7_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___x_11_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_ctor_set(v___x_11_, 2, v___x_10_);
lean_ctor_set(v___x_11_, 3, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_12_; lean_object* v___f_13_; 
v___x_12_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___f_13_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_13_, 0, v___x_12_);
return v___f_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; 
v___f_15_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___x_16_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg(lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_23_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_22_, v_a_19_, v_a_20_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg___boxed(lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v_a_24_, v_a_25_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches(lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v_a_28_, v_a_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___boxed(lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_Grind_BVDecide_getCaches(v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec(v_a_41_);
lean_dec(v_a_40_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0(lean_object* v_caches_52_, lean_object* v_x_53_){
_start:
{
lean_inc_ref(v_caches_52_);
return v_caches_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed(lean_object* v_caches_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0(v_caches_54_, v_x_55_);
lean_dec_ref(v_x_55_);
lean_dec_ref(v_caches_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg(lean_object* v_caches_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___f_60_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_60_, 0, v_caches_57_);
v___x_61_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_62_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_61_, v___f_60_, v_a_58_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___boxed(lean_object* v_caches_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_Grind_BVDecide_setCaches___redArg(v_caches_63_, v_a_64_);
lean_dec(v_a_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches(lean_object* v_caches_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___f_79_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_79_, 0, v_caches_67_);
v___x_80_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_81_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_80_, v___f_79_, v_a_68_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___boxed(lean_object* v_caches_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Grind_BVDecide_setCaches(v_caches_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec(v_a_83_);
return v_res_94_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_BVDecide_bvExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_BVDecide_bvExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
}
#ifdef __cplusplus
}
#endif
