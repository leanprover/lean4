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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(lean_object* v___x_1_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v_res_4_;
v_res_4_ = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(v___x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed(lean_object* v___x_5_, lean_object* v___y_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(v___x_5_);
return v_res_7_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_8_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
lean_ctor_set(v___x_12_, 3, v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_13_; lean_object* v___f_14_; 
v___x_13_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___f_14_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_14_, 0, v___x_13_);
return v___f_14_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; 
v___f_16_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_);
v___x_17_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_16_);
return v___x_17_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_18_;
v_res_18_ = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_();
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2____boxed(lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Meta_Tactic_Grind_BVDecide_Types_0__Lean_Meta_Grind_BVDecide_initFn_00___x40_Lean_Meta_Tactic_Grind_BVDecide_Types_499943386____hygCtx___hyg_2_();
return v_res_20_;
}
}
lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg(lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_25_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_24_, v_a_21_, v_a_22_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_BVDecide_getCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_21_ = stack[0].m_obj;
lean_object* v_a_22_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v_a_21_, v_a_22_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg___boxed(lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v_a_27_, v_a_28_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
return v_res_30_;
}
}
lean_object* l_Lean_Meta_Grind_BVDecide_getCaches(lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v_a_31_, v_a_39_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_BVDecide_getCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_31_ = stack[0].m_obj;
lean_object* v_a_32_ = stack[1].m_obj;
lean_object* v_a_33_ = stack[2].m_obj;
lean_object* v_a_34_ = stack[3].m_obj;
lean_object* v_a_35_ = stack[4].m_obj;
lean_object* v_a_36_ = stack[5].m_obj;
lean_object* v_a_37_ = stack[6].m_obj;
lean_object* v_a_38_ = stack[7].m_obj;
lean_object* v_a_39_ = stack[8].m_obj;
lean_object* v_a_40_ = stack[9].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_Meta_Grind_BVDecide_getCaches(v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___boxed(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Grind_BVDecide_getCaches(v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec(v_a_44_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0(lean_object* v_caches_56_, lean_object* v_x_57_){
_start:
{
lean_inc_ref(v_caches_56_);
return v_caches_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed(lean_object* v_caches_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0(v_caches_58_, v_x_59_);
lean_dec_ref(v_x_59_);
lean_dec_ref(v_caches_58_);
return v_res_60_;
}
}
lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg(lean_object* v_caches_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___f_64_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_64_, 0, v_caches_61_);
v___x_65_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_66_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_65_, v___f_64_, v_a_62_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_BVDecide_setCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caches_61_ = stack[0].m_obj;
lean_object* v_a_62_ = stack[1].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Meta_Grind_BVDecide_setCaches___redArg(v_caches_61_, v_a_62_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___redArg___boxed(lean_object* v_caches_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_Grind_BVDecide_setCaches___redArg(v_caches_68_, v_a_69_);
lean_dec(v_a_69_);
return v_res_71_;
}
}
lean_object* l_Lean_Meta_Grind_BVDecide_setCaches(lean_object* v_caches_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_BVDecide_setCaches___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_84_, 0, v_caches_72_);
v___x_85_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_86_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_85_, v___f_84_, v_a_73_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_BVDecide_setCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_caches_72_ = stack[0].m_obj;
lean_object* v_a_73_ = stack[1].m_obj;
lean_object* v_a_74_ = stack[2].m_obj;
lean_object* v_a_75_ = stack[3].m_obj;
lean_object* v_a_76_ = stack[4].m_obj;
lean_object* v_a_77_ = stack[5].m_obj;
lean_object* v_a_78_ = stack[6].m_obj;
lean_object* v_a_79_ = stack[7].m_obj;
lean_object* v_a_80_ = stack[8].m_obj;
lean_object* v_a_81_ = stack[9].m_obj;
lean_object* v_a_82_ = stack[10].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_Grind_BVDecide_setCaches(v_caches_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_BVDecide_setCaches___boxed(lean_object* v_caches_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Grind_BVDecide_setCaches(v_caches_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec(v_a_89_);
return v_res_100_;
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
