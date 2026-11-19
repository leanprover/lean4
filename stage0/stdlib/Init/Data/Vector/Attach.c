// Lean compiler output
// Module: Init.Data.Vector.Attach
// Imports: public import Init.Data.Vector.Lemmas import all Init.Data.Array.Attach
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_attach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_attach___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__0 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__0_value;
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__1 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__1_value;
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__2 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__2_value;
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__3 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__3_value;
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__4 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__4_value;
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__5 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__5_value;
static const lean_closure_object l_Vector_pmapImpl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_pmapImpl___redArg___closed__6 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__6_value;
static const lean_ctor_object l_Vector_pmapImpl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_pmapImpl___redArg___closed__0_value),((lean_object*)&l_Vector_pmapImpl___redArg___closed__1_value)}};
static const lean_object* l_Vector_pmapImpl___redArg___closed__7 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__7_value;
static const lean_ctor_object l_Vector_pmapImpl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_pmapImpl___redArg___closed__7_value),((lean_object*)&l_Vector_pmapImpl___redArg___closed__2_value),((lean_object*)&l_Vector_pmapImpl___redArg___closed__3_value),((lean_object*)&l_Vector_pmapImpl___redArg___closed__4_value),((lean_object*)&l_Vector_pmapImpl___redArg___closed__5_value)}};
static const lean_object* l_Vector_pmapImpl___redArg___closed__8 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__8_value;
static const lean_ctor_object l_Vector_pmapImpl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_pmapImpl___redArg___closed__8_value),((lean_object*)&l_Vector_pmapImpl___redArg___closed__6_value)}};
static const lean_object* l_Vector_pmapImpl___redArg___closed__9 = (const lean_object*)&l_Vector_pmapImpl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pmapImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pmapImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_unattach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unattach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(lean_object* v_xs_1_){
_start:
{
lean_inc_ref(v_xs_1_);
return v_xs_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg___boxed(lean_object* v_xs_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(v_xs_2_);
lean_dec_ref(v_xs_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(lean_object* v_00_u03b1_4_, lean_object* v_n_5_, lean_object* v_xs_6_, lean_object* v_P_7_, lean_object* v_x_8_){
_start:
{
lean_inc_ref(v_xs_6_);
return v_xs_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___boxed(lean_object* v_00_u03b1_9_, lean_object* v_n_10_, lean_object* v_xs_11_, lean_object* v_P_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(v_00_u03b1_9_, v_n_10_, v_xs_11_, v_P_12_, v_x_13_);
lean_dec_ref(v_xs_11_);
lean_dec(v_n_10_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___redArg(lean_object* v_xs_15_){
_start:
{
lean_inc_ref(v_xs_15_);
return v_xs_15_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___redArg___boxed(lean_object* v_xs_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Vector_attach___redArg(v_xs_16_);
lean_dec_ref(v_xs_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach(lean_object* v_00_u03b1_18_, lean_object* v_n_19_, lean_object* v_xs_20_){
_start:
{
lean_inc_ref(v_xs_20_);
return v_xs_20_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___boxed(lean_object* v_00_u03b1_21_, lean_object* v_n_22_, lean_object* v_xs_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Vector_attach(v_00_u03b1_21_, v_n_22_, v_xs_23_);
lean_dec_ref(v_xs_23_);
lean_dec(v_n_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg___lam__0(lean_object* v_f_25_, lean_object* v_x_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_2(v_f_25_, v_x_26_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg(lean_object* v_f_47_, lean_object* v_xs_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; size_t v_sz_51_; size_t v___x_52_; lean_object* v___x_53_; 
v___f_49_ = lean_alloc_closure((void*)(l_Vector_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_49_, 0, v_f_47_);
v___x_50_ = ((lean_object*)(l_Vector_pmapImpl___redArg___closed__9));
v_sz_51_ = lean_array_size(v_xs_48_);
v___x_52_ = ((size_t)0ULL);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_50_, v___f_49_, v_sz_51_, v___x_52_, v_xs_48_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_n_56_, lean_object* v_P_57_, lean_object* v_f_58_, lean_object* v_xs_59_, lean_object* v_H_60_){
_start:
{
lean_object* v___f_61_; lean_object* v___x_62_; size_t v_sz_63_; size_t v___x_64_; lean_object* v___x_65_; 
v___f_61_ = lean_alloc_closure((void*)(l_Vector_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_61_, 0, v_f_58_);
v___x_62_ = ((lean_object*)(l_Vector_pmapImpl___redArg___closed__9));
v_sz_63_ = lean_array_size(v_xs_59_);
v___x_64_ = ((size_t)0ULL);
v___x_65_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_62_, v___f_61_, v_sz_63_, v___x_64_, v_xs_59_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___boxed(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_n_68_, lean_object* v_P_69_, lean_object* v_f_70_, lean_object* v_xs_71_, lean_object* v_H_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Vector_pmapImpl(v_00_u03b1_66_, v_00_u03b2_67_, v_n_68_, v_P_69_, v_f_70_, v_xs_71_, v_H_72_);
lean_dec(v_n_68_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach___redArg(lean_object* v_xs_74_){
_start:
{
size_t v_sz_75_; size_t v___x_76_; lean_object* v___x_77_; 
v_sz_75_ = lean_array_size(v_xs_74_);
v___x_76_ = ((size_t)0ULL);
v___x_77_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_75_, v___x_76_, v_xs_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach(lean_object* v_n_78_, lean_object* v_00_u03b1_79_, lean_object* v_p_80_, lean_object* v_xs_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Vector_unattach___redArg(v_xs_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach___boxed(lean_object* v_n_83_, lean_object* v_00_u03b1_84_, lean_object* v_p_85_, lean_object* v_xs_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Vector_unattach(v_n_83_, v_00_u03b1_84_, v_p_85_, v_xs_86_);
lean_dec(v_n_83_);
return v_res_87_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
