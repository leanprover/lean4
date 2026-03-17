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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object* v_s_1_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object* v_s_4_){
_start:
{
uint8_t v_res_5_; lean_object* v_r_6_; 
v_res_5_ = l_Lean_Meta_MVarRenaming_isEmpty(v_s_4_);
lean_dec(v_s_4_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
lean_object* v_k_9_; lean_object* v_v_10_; lean_object* v_l_11_; lean_object* v_r_12_; uint8_t v___x_13_; 
v_k_9_ = lean_ctor_get(v_t_7_, 1);
v_v_10_ = lean_ctor_get(v_t_7_, 2);
v_l_11_ = lean_ctor_get(v_t_7_, 3);
v_r_12_ = lean_ctor_get(v_t_7_, 4);
v___x_13_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_8_, v_k_9_);
switch(v___x_13_)
{
case 0:
{
v_t_7_ = v_l_11_;
goto _start;
}
case 1:
{
lean_object* v___x_15_; 
lean_inc(v_v_10_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v_v_10_);
return v___x_15_;
}
default: 
{
v_t_7_ = v_r_12_;
goto _start;
}
}
}
else
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg___boxed(lean_object* v_t_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_t_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_t_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object* v_s_21_, lean_object* v_mvarId_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_21_, v_mvarId_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object* v_s_24_, lean_object* v_mvarId_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_MVarRenaming_find_x3f(v_s_24_, v_mvarId_25_);
lean_dec(v_mvarId_25_);
lean_dec(v_s_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(lean_object* v_00_u03b4_27_, lean_object* v_t_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_t_28_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___boxed(lean_object* v_00_u03b4_31_, lean_object* v_t_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(v_00_u03b4_31_, v_t_32_, v_k_33_);
lean_dec(v_k_33_);
lean_dec(v_t_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(lean_object* v_msg_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_box(0);
v___x_37_ = lean_panic_fn(v___x_36_, v_msg_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_41_ = ((lean_object*)(l_Lean_Meta_MVarRenaming_find_x21___closed__2));
v___x_42_ = lean_unsigned_to_nat(14u);
v___x_43_ = lean_unsigned_to_nat(22u);
v___x_44_ = ((lean_object*)(l_Lean_Meta_MVarRenaming_find_x21___closed__1));
v___x_45_ = ((lean_object*)(l_Lean_Meta_MVarRenaming_find_x21___closed__0));
v___x_46_ = l_mkPanicMessageWithDecl(v___x_45_, v___x_44_, v___x_43_, v___x_42_, v___x_41_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object* v_s_47_, lean_object* v_mvarId_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_47_, v_mvarId_48_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_MVarRenaming_find_x21___closed__3, &l_Lean_Meta_MVarRenaming_find_x21___closed__3_once, _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3);
v___x_51_ = l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(v___x_50_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; 
v_val_52_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_52_);
lean_dec_ref(v___x_49_);
return v_val_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object* v_s_53_, lean_object* v_mvarId_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_MVarRenaming_find_x21(v_s_53_, v_mvarId_54_);
lean_dec(v_mvarId_54_);
lean_dec(v_s_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object* v_s_56_, lean_object* v_mvarId_57_, lean_object* v_mvarId_x27_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_57_, v_mvarId_x27_58_, v_s_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lam__0(lean_object* v_s_60_, lean_object* v_e_61_){
_start:
{
if (lean_obj_tag(v_e_61_) == 2)
{
lean_object* v_mvarId_62_; lean_object* v___x_63_; 
v_mvarId_62_ = lean_ctor_get(v_e_61_, 0);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_60_, v_mvarId_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; 
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v_e_61_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_73_; 
lean_dec_ref(v_e_61_);
v_val_65_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_73_ == 0)
{
v___x_67_ = v___x_63_;
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_val_65_);
lean_dec(v___x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = l_Lean_mkMVar(v_val_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_69_);
v___x_71_ = v___x_67_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
else
{
lean_object* v___x_74_; 
lean_dec_ref(v_e_61_);
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___lam__0___boxed(lean_object* v_s_75_, lean_object* v_e_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_MVarRenaming_apply___lam__0(v_s_75_, v_e_76_);
lean_dec(v_s_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object* v_s_78_, lean_object* v_e_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Lean_Expr_hasMVar(v_e_79_);
if (v___x_80_ == 0)
{
lean_dec(v_s_78_);
lean_inc_ref(v_e_79_);
return v_e_79_;
}
else
{
if (lean_obj_tag(v_s_78_) == 0)
{
lean_object* v___f_81_; lean_object* v___x_82_; 
v___f_81_ = lean_alloc_closure((void*)(l_Lean_Meta_MVarRenaming_apply___lam__0___boxed), 2, 1);
lean_closure_set(v___f_81_, 0, v_s_78_);
v___x_82_ = lean_replace_expr(v___f_81_, v_e_79_);
lean_dec_ref(v___f_81_);
return v___x_82_;
}
else
{
lean_inc_ref(v_e_79_);
return v_e_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object* v_s_83_, lean_object* v_e_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_MVarRenaming_apply(v_s_83_, v_e_84_);
lean_dec_ref(v_e_84_);
return v_res_85_;
}
}
lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
