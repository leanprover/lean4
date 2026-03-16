// Lean compiler output
// Module: Lean.Util.FVarSubset
// Imports: public import Lean.Util.CollectFVars public import Lean.Util.FindExpr
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_find_ext_expr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_fvarsSubset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_fvarsSubset___closed__0;
static lean_once_cell_t l_Lean_Expr_fvarsSubset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_fvarsSubset___closed__1;
static const lean_array_object l_Lean_Expr_fvarsSubset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_fvarsSubset___closed__2 = (const lean_object*)&l_Lean_Expr_fvarsSubset___closed__2_value;
static lean_once_cell_t l_Lean_Expr_fvarsSubset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_fvarsSubset___closed__3;
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_l_4_; lean_object* v_r_5_; uint8_t v___x_6_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
v_l_4_ = lean_ctor_get(v_t_2_, 3);
v_r_5_ = lean_ctor_get(v_t_2_, 4);
v___x_6_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1_, v_k_3_);
switch(v___x_6_)
{
case 0:
{
v_t_2_ = v_l_4_;
goto _start;
}
case 1:
{
uint8_t v___x_8_; 
v___x_8_ = 1;
return v___x_8_;
}
default: 
{
v_t_2_ = v_r_5_;
goto _start;
}
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg___boxed(lean_object* v_k_11_, lean_object* v_t_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(v_k_11_, v_t_12_);
lean_dec(v_t_12_);
lean_dec(v_k_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset___lam__0(lean_object* v_s_15_, lean_object* v_e_16_){
_start:
{
uint8_t v___y_18_; uint8_t v___x_21_; 
v___x_21_ = l_Lean_Expr_hasFVar(v_e_16_);
if (v___x_21_ == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 2;
return v___x_22_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = l_Lean_Expr_isFVar(v_e_16_);
if (v___x_23_ == 0)
{
v___y_18_ = v___x_23_;
goto v___jp_17_;
}
else
{
lean_object* v_fvarSet_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_fvarSet_24_ = lean_ctor_get(v_s_15_, 1);
v___x_25_ = l_Lean_Expr_fvarId_x21(v_e_16_);
v___x_26_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(v___x_25_, v_fvarSet_24_);
lean_dec(v___x_25_);
if (v___x_26_ == 0)
{
v___y_18_ = v___x_23_;
goto v___jp_17_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = 1;
return v___x_27_;
}
}
}
v___jp_17_:
{
if (v___y_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 1;
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___lam__0___boxed(lean_object* v_s_28_, lean_object* v_e_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Expr_fvarsSubset___lam__0(v_s_28_, v_e_29_);
lean_dec_ref(v_e_29_);
lean_dec_ref(v_s_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__0(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = lean_mk_array(v___x_33_, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__1(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l_Lean_Expr_fvarsSubset___closed__0, &l_Lean_Expr_fvarsSubset___closed__0_once, _init_l_Lean_Expr_fvarsSubset___closed__0);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = ((lean_object*)(l_Lean_Expr_fvarsSubset___closed__2));
v___x_41_ = lean_box(1);
v___x_42_ = lean_obj_once(&l_Lean_Expr_fvarsSubset___closed__1, &l_Lean_Expr_fvarsSubset___closed__1_once, _init_l_Lean_Expr_fvarsSubset___closed__1);
v___x_43_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___x_40_);
return v___x_43_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset(lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_Expr_hasFVar(v_a_44_);
if (v___x_46_ == 0)
{
uint8_t v___x_47_; 
lean_dec_ref(v_b_45_);
v___x_47_ = 1;
return v___x_47_;
}
else
{
uint8_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = 0;
v___x_49_ = l_Lean_Expr_hasFVar(v_b_45_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_b_45_);
return v___x_48_;
}
else
{
lean_object* v___x_50_; lean_object* v_s_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v___x_50_ = lean_obj_once(&l_Lean_Expr_fvarsSubset___closed__3, &l_Lean_Expr_fvarsSubset___closed__3_once, _init_l_Lean_Expr_fvarsSubset___closed__3);
v_s_51_ = l_Lean_collectFVars(v___x_50_, v_b_45_);
v___f_52_ = lean_alloc_closure((void*)(l_Lean_Expr_fvarsSubset___lam__0___boxed), 2, 1);
lean_closure_set(v___f_52_, 0, v_s_51_);
v___x_53_ = lean_find_ext_expr(v___f_52_, v_a_44_);
lean_dec_ref(v___f_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
return v___x_49_;
}
else
{
lean_dec_ref(v___x_53_);
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___boxed(lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Expr_fvarsSubset(v_a_54_, v_b_55_);
lean_dec_ref(v_a_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0(lean_object* v_00_u03b2_58_, lean_object* v_k_59_, lean_object* v_t_60_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(v_k_59_, v_t_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___boxed(lean_object* v_00_u03b2_62_, lean_object* v_k_63_, lean_object* v_t_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0(v_00_u03b2_62_, v_k_63_, v_t_64_);
lean_dec(v_t_64_);
lean_dec(v_k_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_FindExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_FVarSubset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_FVarSubset(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FVarSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_FVarSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_FVarSubset(builtin);
}
#ifdef __cplusplus
}
#endif
