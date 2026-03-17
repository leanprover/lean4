// Lean compiler output
// Module: Lake.Build.Target.Basic
// Imports: public import Lake.Build.Key
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
lean_object* l_Lake_instReprBuildKey_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
static const lean_string_object l_Lake_Target_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Target.mk"};
static const lean_object* l_Lake_Target_repr___redArg___closed__0 = (const lean_object*)&l_Lake_Target_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Target_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Target_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_Target_repr___redArg___closed__1 = (const lean_object*)&l_Lake_Target_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_Target_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_Target_repr___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Target_repr___redArg___closed__2 = (const lean_object*)&l_Lake_Target_repr___redArg___closed__2_value;
static lean_once_cell_t l_Lake_Target_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Target_repr___redArg___closed__3;
static lean_once_cell_t l_Lake_Target_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Target_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Target_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Target_repr___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_Target_instRepr___closed__0 = (const lean_object*)&l_Lake_Target_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Target_instRepr(lean_object*);
static const lean_closure_object l_Lake_Target_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PartialBuildKey_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Target_instToString___closed__0 = (const lean_object*)&l_Lake_Target_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Target_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_instCoePartialBuildKey___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_instCoePartialBuildKey___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Target_instCoePartialBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Target_instCoePartialBuildKey___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Target_instCoePartialBuildKey___closed__0 = (const lean_object*)&l_Lake_Target_instCoePartialBuildKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Target_instCoePartialBuildKey(lean_object*);
static lean_object* _init_l_Lake_Target_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lake_Target_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_to_int(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg(lean_object* v_x_11_, lean_object* v_prec_12_){
_start:
{
lean_object* v___y_14_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(1024u);
v___x_24_ = lean_nat_dec_le(v___x_23_, v_prec_12_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lake_Target_repr___redArg___closed__3, &l_Lake_Target_repr___redArg___closed__3_once, _init_l_Lake_Target_repr___redArg___closed__3);
v___y_14_ = v___x_25_;
goto v___jp_13_;
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lake_Target_repr___redArg___closed__4, &l_Lake_Target_repr___redArg___closed__4_once, _init_l_Lake_Target_repr___redArg___closed__4);
v___y_14_ = v___x_26_;
goto v___jp_13_;
}
v___jp_13_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_ctor_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_15_ = ((lean_object*)(l_Lake_Target_repr___redArg___closed__2));
v___x_16_ = lean_unsigned_to_nat(1024u);
v___x_17_ = l_Lake_instReprBuildKey_repr(v_x_11_, v___x_16_);
v_ctor_18_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_ctor_18_, 0, v___x_15_);
lean_ctor_set(v_ctor_18_, 1, v___x_17_);
v___x_19_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_19_, 0, v___y_14_);
lean_ctor_set(v___x_19_, 1, v_ctor_18_);
v___x_20_ = 0;
v___x_21_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_21_, 0, v___x_19_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*1, v___x_20_);
v___x_22_ = l_Repr_addAppParen(v___x_21_, v_prec_12_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg___boxed(lean_object* v_x_27_, lean_object* v_prec_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_Target_repr___redArg(v_x_27_, v_prec_28_);
lean_dec(v_prec_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr(lean_object* v_00_u03b1_30_, lean_object* v_x_31_, lean_object* v_prec_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lake_Target_repr___redArg(v_x_31_, v_prec_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___boxed(lean_object* v_00_u03b1_34_, lean_object* v_x_35_, lean_object* v_prec_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_Target_repr(v_00_u03b1_34_, v_x_35_, v_prec_36_);
lean_dec(v_prec_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_instRepr(lean_object* v_00_u03b1_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_Lake_Target_instRepr___closed__0));
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_instToString(lean_object* v_00_u03b1_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = ((lean_object*)(l_Lake_Target_instToString___closed__0));
return v___f_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_instCoePartialBuildKey___lam__0(lean_object* v_key_44_){
_start:
{
lean_inc_ref(v_key_44_);
return v_key_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_instCoePartialBuildKey___lam__0___boxed(lean_object* v_key_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_Target_instCoePartialBuildKey___lam__0(v_key_45_);
lean_dec_ref(v_key_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_instCoePartialBuildKey(lean_object* v_00_u03b1_48_){
_start:
{
lean_object* v___f_49_; 
v___f_49_ = ((lean_object*)(l_Lake_Target_instCoePartialBuildKey___closed__0));
return v___f_49_;
}
}
lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Target_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Target_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Key(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Target_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Target_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Target_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Target_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
