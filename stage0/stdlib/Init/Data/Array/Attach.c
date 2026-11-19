// Lean compiler output
// Module: Init.Data.Array.Attach
// Imports: import all Init.Data.List.Attach public import Init.Data.Array.Lemmas import Init.Data.Array.Bootstrap import Init.Data.Array.Count
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_pmapImpl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__0 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__0_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__1 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__1_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__2 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__2_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__3 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__3_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__4 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__4_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__5 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__5_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__6 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__6_value;
static const lean_ctor_object l_Array_pmapImpl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_pmapImpl___redArg___closed__0_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__1_value)}};
static const lean_object* l_Array_pmapImpl___redArg___closed__7 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__7_value;
static const lean_ctor_object l_Array_pmapImpl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_pmapImpl___redArg___closed__7_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__2_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__3_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__4_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__5_value)}};
static const lean_object* l_Array_pmapImpl___redArg___closed__8 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__8_value;
static const lean_ctor_object l_Array_pmapImpl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_pmapImpl___redArg___closed__8_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__6_value)}};
static const lean_object* l_Array_pmapImpl___redArg___closed__9 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmapImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(lean_object* v_xs_1_){
_start:
{
lean_inc_ref(v_xs_1_);
return v_xs_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(lean_object* v_xs_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(v_xs_2_);
lean_dec_ref(v_xs_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(lean_object* v_00_u03b1_4_, lean_object* v_xs_5_, lean_object* v_P_6_, lean_object* v_x_7_){
_start:
{
lean_inc_ref(v_xs_5_);
return v_xs_5_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_xs_9_, lean_object* v_P_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(v_00_u03b1_8_, v_xs_9_, v_P_10_, v_x_11_);
lean_dec_ref(v_xs_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Array_attach___redArg(lean_object* v_xs_13_){
_start:
{
lean_inc_ref(v_xs_13_);
return v_xs_13_;
}
}
LEAN_EXPORT lean_object* l_Array_attach___redArg___boxed(lean_object* v_xs_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Array_attach___redArg(v_xs_14_);
lean_dec_ref(v_xs_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Array_attach(lean_object* v_00_u03b1_16_, lean_object* v_xs_17_){
_start:
{
lean_inc_ref(v_xs_17_);
return v_xs_17_;
}
}
LEAN_EXPORT lean_object* l_Array_attach___boxed(lean_object* v_00_u03b1_18_, lean_object* v_xs_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Array_attach(v_00_u03b1_18_, v_xs_19_);
lean_dec_ref(v_xs_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg___lam__0(lean_object* v_f_21_, lean_object* v_x_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_2(v_f_21_, v_x_22_, lean_box(0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg(lean_object* v_f_43_, lean_object* v_xs_44_){
_start:
{
lean_object* v___f_45_; lean_object* v___x_46_; size_t v_sz_47_; size_t v___x_48_; lean_object* v___x_49_; 
v___f_45_ = lean_alloc_closure((void*)(l_Array_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_45_, 0, v_f_43_);
v___x_46_ = ((lean_object*)(l_Array_pmapImpl___redArg___closed__9));
v_sz_47_ = lean_array_size(v_xs_44_);
v___x_48_ = ((size_t)0ULL);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_46_, v___f_45_, v_sz_47_, v___x_48_, v_xs_44_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Array_pmapImpl(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_P_52_, lean_object* v_f_53_, lean_object* v_xs_54_, lean_object* v_H_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; size_t v_sz_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___f_56_ = lean_alloc_closure((void*)(l_Array_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_56_, 0, v_f_53_);
v___x_57_ = ((lean_object*)(l_Array_pmapImpl___redArg___closed__9));
v_sz_58_ = lean_array_size(v_xs_54_);
v___x_59_ = ((size_t)0ULL);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_57_, v___f_56_, v_sz_58_, v___x_59_, v_xs_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(size_t v_sz_61_, size_t v_i_62_, lean_object* v_bs_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = lean_usize_dec_lt(v_i_62_, v_sz_61_);
if (v___x_64_ == 0)
{
return v_bs_63_;
}
else
{
lean_object* v_v_65_; lean_object* v___x_66_; lean_object* v_bs_x27_67_; size_t v___x_68_; size_t v___x_69_; lean_object* v___x_70_; 
v_v_65_ = lean_array_uget(v_bs_63_, v_i_62_);
v___x_66_ = lean_unsigned_to_nat(0u);
v_bs_x27_67_ = lean_array_uset(v_bs_63_, v_i_62_, v___x_66_);
v___x_68_ = ((size_t)1ULL);
v___x_69_ = lean_usize_add(v_i_62_, v___x_68_);
v___x_70_ = lean_array_uset(v_bs_x27_67_, v_i_62_, v_v_65_);
v_i_62_ = v___x_69_;
v_bs_63_ = v___x_70_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg___boxed(lean_object* v_sz_72_, lean_object* v_i_73_, lean_object* v_bs_74_){
_start:
{
size_t v_sz_boxed_75_; size_t v_i_boxed_76_; lean_object* v_res_77_; 
v_sz_boxed_75_ = lean_unbox_usize(v_sz_72_);
lean_dec(v_sz_72_);
v_i_boxed_76_ = lean_unbox_usize(v_i_73_);
lean_dec(v_i_73_);
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_boxed_75_, v_i_boxed_76_, v_bs_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Array_unattach___redArg(lean_object* v_xs_78_){
_start:
{
size_t v_sz_79_; size_t v___x_80_; lean_object* v___x_81_; 
v_sz_79_ = lean_array_size(v_xs_78_);
v___x_80_ = ((size_t)0ULL);
v___x_81_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_79_, v___x_80_, v_xs_78_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Array_unattach(lean_object* v_00_u03b1_82_, lean_object* v_p_83_, lean_object* v_xs_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Array_unattach___redArg(v_xs_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(lean_object* v_00_u03b1_86_, size_t v_sz_87_, size_t v_i_88_, lean_object* v_bs_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_87_, v_i_88_, v_bs_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___boxed(lean_object* v_00_u03b1_91_, lean_object* v_sz_92_, lean_object* v_i_93_, lean_object* v_bs_94_){
_start:
{
size_t v_sz_boxed_95_; size_t v_i_boxed_96_; lean_object* v_res_97_; 
v_sz_boxed_95_ = lean_unbox_usize(v_sz_92_);
lean_dec(v_sz_92_);
v_i_boxed_96_ = lean_unbox_usize(v_i_93_);
lean_dec(v_i_93_);
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(v_00_u03b1_91_, v_sz_boxed_95_, v_i_boxed_96_, v_bs_94_);
return v_res_97_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Count(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Count(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
