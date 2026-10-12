// Lean compiler output
// Module: Lean.Meta.Match.MVarRenaming
// Imports: public import Lean.Util.ReplaceExpr
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_MVarRenaming_find_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__0 = (const lean_object*)&l_Lean_Meta_MVarRenaming_find_x21___closed__0_value;
static const lean_string_object l_Lean_Meta_MVarRenaming_find_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__1 = (const lean_object*)&l_Lean_Meta_MVarRenaming_find_x21___closed__1_value;
static const lean_string_object l_Lean_Meta_MVarRenaming_find_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__2 = (const lean_object*)&l_Lean_Meta_MVarRenaming_find_x21___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MVarRenaming_find_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object* v_s_1_){
_start:
{
if (lean_obj_tag(v_s_1_) == 0)
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
else
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MVarRenaming_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1_ = stack[0].m_obj;
uint8_t v_res_4_;
v_res_4_ = l_Lean_Meta_MVarRenaming_isEmpty(v_s_1_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object* v_s_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lean_Meta_MVarRenaming_isEmpty(v_s_5_);
lean_dec(v_s_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 0)
{
lean_object* v_k_10_; lean_object* v_v_11_; lean_object* v_l_12_; lean_object* v_r_13_; uint8_t v___x_14_; 
v_k_10_ = lean_ctor_get(v_t_8_, 1);
v_v_11_ = lean_ctor_get(v_t_8_, 2);
v_l_12_ = lean_ctor_get(v_t_8_, 3);
v_r_13_ = lean_ctor_get(v_t_8_, 4);
v___x_14_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_9_, v_k_10_);
switch(v___x_14_)
{
case 0:
{
v_t_8_ = v_l_12_;
goto _start;
}
case 1:
{
lean_object* v___x_16_; 
lean_inc(v_v_11_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v_v_11_);
return v___x_16_;
}
default: 
{
v_t_8_ = v_r_13_;
goto _start;
}
}
}
else
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg___boxed(lean_object* v_t_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_t_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_t_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object* v_s_22_, lean_object* v_mvarId_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_22_, v_mvarId_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object* v_s_25_, lean_object* v_mvarId_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_MVarRenaming_find_x3f(v_s_25_, v_mvarId_26_);
lean_dec(v_mvarId_26_);
lean_dec(v_s_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(lean_object* v_00_u03b4_28_, lean_object* v_t_29_, lean_object* v_k_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_t_29_, v_k_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___boxed(lean_object* v_00_u03b4_32_, lean_object* v_t_33_, lean_object* v_k_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(v_00_u03b4_32_, v_t_33_, v_k_34_);
lean_dec(v_k_34_);
lean_dec(v_t_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(lean_object* v_msg_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_panic_fn_borrowed(v___x_37_, v_msg_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_42_ = ((lean_object*)(l_Lean_Meta_MVarRenaming_find_x21___closed__2));
v___x_43_ = lean_unsigned_to_nat(14u);
v___x_44_ = lean_unsigned_to_nat(22u);
v___x_45_ = ((lean_object*)(l_Lean_Meta_MVarRenaming_find_x21___closed__1));
v___x_46_ = ((lean_object*)(l_Lean_Meta_MVarRenaming_find_x21___closed__0));
v___x_47_ = l_mkPanicMessageWithDecl(v___x_46_, v___x_45_, v___x_44_, v___x_43_, v___x_42_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object* v_s_48_, lean_object* v_mvarId_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_48_, v_mvarId_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Lean_Meta_MVarRenaming_find_x21___closed__3, &l_Lean_Meta_MVarRenaming_find_x21___closed__3_once, _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3);
v___x_52_ = l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_val_53_; 
v_val_53_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v___x_50_, 1);
return v_val_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object* v_s_54_, lean_object* v_mvarId_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_MVarRenaming_find_x21(v_s_54_, v_mvarId_55_);
lean_dec(v_mvarId_55_);
lean_dec(v_s_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object* v_s_57_, lean_object* v_mvarId_58_, lean_object* v_mvarId_x27_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_58_, v_mvarId_x27_59_, v_s_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lam__0(lean_object* v_s_61_, lean_object* v_e_62_){
_start:
{
if (lean_obj_tag(v_e_62_) == 2)
{
lean_object* v_mvarId_63_; lean_object* v___x_64_; 
v_mvarId_63_ = lean_ctor_get(v_e_62_, 0);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_61_, v_mvarId_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v_e_62_);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
lean_dec_ref_known(v_e_62_, 1);
v_val_66_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_64_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_dec(v___x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = l_Lean_mkMVar(v_val_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v___x_75_; 
lean_dec_ref(v_e_62_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lam__0___boxed(lean_object* v_s_76_, lean_object* v_e_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Meta_MVarRenaming_apply___lam__0(v_s_76_, v_e_77_);
lean_dec(v_s_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object* v_s_79_, lean_object* v_e_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_Expr_hasMVar(v_e_80_);
if (v___x_81_ == 0)
{
lean_dec(v_s_79_);
lean_inc_ref(v_e_80_);
return v_e_80_;
}
else
{
if (lean_obj_tag(v_s_79_) == 0)
{
lean_object* v___f_82_; lean_object* v___x_83_; 
v___f_82_ = lean_alloc_closure((void*)(l_Lean_Meta_MVarRenaming_apply___lam__0___boxed), 2, 1);
lean_closure_set(v___f_82_, 0, v_s_79_);
v___x_83_ = lean_replace_expr(v___f_82_, v_e_80_);
lean_dec_ref(v___f_82_);
return v___x_83_;
}
else
{
lean_inc_ref(v_e_80_);
return v_e_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object* v_s_84_, lean_object* v_e_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Meta_MVarRenaming_apply(v_s_84_, v_e_85_);
lean_dec_ref(v_e_85_);
return v_res_86_;
}
}
lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MVarRenaming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MVarRenaming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MVarRenaming(builtin);
}
#ifdef __cplusplus
}
#endif
