// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadCanon
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_e_3_){
_start:
{
lean_object* v_canonExpr_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_canonExpr_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc(v_canonExpr_4_);
lean_dec_ref(v_inst_1_);
v___x_5_ = lean_apply_1(v_canonExpr_4_, v_e_3_);
v___x_6_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1(lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_e_9_){
_start:
{
lean_object* v_synthInstance_x3f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_synthInstance_x3f_10_ = lean_ctor_get(v_inst_7_, 1);
lean_inc(v_synthInstance_x3f_10_);
lean_dec_ref(v_inst_7_);
v___x_11_ = lean_apply_1(v_synthInstance_x3f_10_, v_e_9_);
v___x_12_ = lean_apply_2(v_inst_8_, lean_box(0), v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg(lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; 
lean_inc(v_inst_13_);
lean_inc_ref(v_inst_14_);
v___f_15_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_15_, 0, v_inst_14_);
lean_closure_set(v___f_15_, 1, v_inst_13_);
v___f_16_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_16_, 0, v_inst_14_);
lean_closure_set(v___f_16_, 1, v_inst_13_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___f_15_);
lean_ctor_set(v___x_17_, 1, v___f_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift(lean_object* v_m_18_, lean_object* v_n_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; 
lean_inc(v_inst_20_);
lean_inc_ref(v_inst_21_);
v___f_22_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_inst_21_);
lean_closure_set(v___f_22_, 1, v_inst_20_);
v___f_23_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_23_, 0, v_inst_21_);
lean_closure_set(v___f_23_, 1, v_inst_20_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___f_22_);
lean_ctor_set(v___x_24_, 1, v___f_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0));
v___x_27_ = l_Lean_stringToMessageData(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0(lean_object* v_toPure_28_, lean_object* v_type_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_____x_32_){
_start:
{
if (lean_obj_tag(v_____x_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_34_; 
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_type_29_);
v_val_33_ = lean_ctor_get(v_____x_32_, 0);
lean_inc(v_val_33_);
lean_dec_ref(v_____x_32_);
v___x_34_ = lean_apply_2(v_toPure_28_, lean_box(0), v_val_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec(v_____x_32_);
lean_dec(v_toPure_28_);
v___x_35_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1);
v___x_36_ = l_Lean_indentExpr(v_type_29_);
v___x_37_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = l_Lean_throwError___redArg(v_inst_30_, v_inst_31_, v___x_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_type_42_){
_start:
{
lean_object* v_toApplicative_43_; lean_object* v_toBind_44_; lean_object* v_synthInstance_x3f_45_; lean_object* v_toPure_46_; lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v_toApplicative_43_ = lean_ctor_get(v_inst_39_, 0);
v_toBind_44_ = lean_ctor_get(v_inst_39_, 1);
lean_inc(v_toBind_44_);
v_synthInstance_x3f_45_ = lean_ctor_get(v_inst_41_, 1);
lean_inc(v_synthInstance_x3f_45_);
lean_dec_ref(v_inst_41_);
v_toPure_46_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_46_);
lean_inc_ref(v_type_42_);
v___x_47_ = lean_apply_1(v_synthInstance_x3f_45_, v_type_42_);
v___f_48_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0), 5, 4);
lean_closure_set(v___f_48_, 0, v_toPure_46_);
lean_closure_set(v___f_48_, 1, v_type_42_);
lean_closure_set(v___f_48_, 2, v_inst_39_);
lean_closure_set(v___f_48_, 3, v_inst_40_);
v___x_49_ = lean_apply_4(v_toBind_44_, lean_box(0), lean_box(0), v___x_47_, v___f_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance(lean_object* v_m_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_type_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_51_, v_inst_52_, v_inst_53_, v_type_54_);
return v___x_55_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
}
#ifdef __cplusplus
}
#endif
