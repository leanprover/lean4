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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pmap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(lean_object* v_f_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_5_ == 0)
{
lean_dec(v_f_1_);
return v_bs_4_;
}
else
{
lean_object* v_v_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; lean_object* v___x_12_; 
v_v_6_ = lean_array_uget(v_bs_4_, v_i_3_);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_4_, v_i_3_, v___x_7_);
lean_inc(v_f_1_);
v___x_9_ = lean_apply_2(v_f_1_, v_v_6_, lean_box(0));
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_3_, v___x_10_);
v___x_12_ = lean_array_uset(v_bs_x27_8_, v_i_3_, v___x_9_);
v_i_3_ = v___x_11_;
v_bs_4_ = v___x_12_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg___boxed(lean_object* v_f_14_, lean_object* v_sz_15_, lean_object* v_i_16_, lean_object* v_bs_17_){
_start:
{
size_t v_sz_boxed_18_; size_t v_i_boxed_19_; lean_object* v_res_20_; 
v_sz_boxed_18_ = lean_unbox_usize(v_sz_15_);
lean_dec(v_sz_15_);
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_14_, v_sz_boxed_18_, v_i_boxed_19_, v_bs_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmap___redArg(lean_object* v_f_21_, lean_object* v_xs_22_){
_start:
{
size_t v_sz_23_; size_t v___x_24_; lean_object* v___x_25_; 
v_sz_23_ = lean_array_size(v_xs_22_);
v___x_24_ = ((size_t)0ULL);
v___x_25_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_21_, v_sz_23_, v___x_24_, v_xs_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmap(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_n_28_, lean_object* v_P_29_, lean_object* v_f_30_, lean_object* v_xs_31_, lean_object* v_H_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Vector_pmap___redArg(v_f_30_, v_xs_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmap___boxed(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_n_36_, lean_object* v_P_37_, lean_object* v_f_38_, lean_object* v_xs_39_, lean_object* v_H_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Vector_pmap(v_00_u03b1_34_, v_00_u03b2_35_, v_n_36_, v_P_37_, v_f_38_, v_xs_39_, v_H_40_);
lean_dec(v_n_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_f_44_, size_t v_sz_45_, size_t v_i_46_, lean_object* v_bs_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_44_, v_sz_45_, v_i_46_, v_bs_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___boxed(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_f_51_, lean_object* v_sz_52_, lean_object* v_i_53_, lean_object* v_bs_54_){
_start:
{
size_t v_sz_boxed_55_; size_t v_i_boxed_56_; lean_object* v_res_57_; 
v_sz_boxed_55_ = lean_unbox_usize(v_sz_52_);
lean_dec(v_sz_52_);
v_i_boxed_56_ = lean_unbox_usize(v_i_53_);
lean_dec(v_i_53_);
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(v_00_u03b1_49_, v_00_u03b2_50_, v_f_51_, v_sz_boxed_55_, v_i_boxed_56_, v_bs_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(lean_object* v_xs_58_){
_start:
{
lean_inc_ref(v_xs_58_);
return v_xs_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg___boxed(lean_object* v_xs_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(v_xs_59_);
lean_dec_ref(v_xs_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(lean_object* v_00_u03b1_61_, lean_object* v_n_62_, lean_object* v_xs_63_, lean_object* v_P_64_, lean_object* v_x_65_){
_start:
{
lean_inc_ref(v_xs_63_);
return v_xs_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___boxed(lean_object* v_00_u03b1_66_, lean_object* v_n_67_, lean_object* v_xs_68_, lean_object* v_P_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(v_00_u03b1_66_, v_n_67_, v_xs_68_, v_P_69_, v_x_70_);
lean_dec_ref(v_xs_68_);
lean_dec(v_n_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___redArg(lean_object* v_xs_72_){
_start:
{
lean_inc_ref(v_xs_72_);
return v_xs_72_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___redArg___boxed(lean_object* v_xs_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Vector_attach___redArg(v_xs_73_);
lean_dec_ref(v_xs_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach(lean_object* v_00_u03b1_75_, lean_object* v_n_76_, lean_object* v_xs_77_){
_start:
{
lean_inc_ref(v_xs_77_);
return v_xs_77_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___boxed(lean_object* v_00_u03b1_78_, lean_object* v_n_79_, lean_object* v_xs_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Vector_attach(v_00_u03b1_78_, v_n_79_, v_xs_80_);
lean_dec_ref(v_xs_80_);
lean_dec(v_n_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg___lam__0(lean_object* v_f_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_2(v_f_82_, v_x_83_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg(lean_object* v_f_104_, lean_object* v_xs_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; size_t v_sz_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___f_106_ = lean_alloc_closure((void*)(l_Vector_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_106_, 0, v_f_104_);
v___x_107_ = ((lean_object*)(l_Vector_pmapImpl___redArg___closed__9));
v_sz_108_ = lean_array_size(v_xs_105_);
v___x_109_ = ((size_t)0ULL);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_107_, v___f_106_, v_sz_108_, v___x_109_, v_xs_105_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_n_113_, lean_object* v_P_114_, lean_object* v_f_115_, lean_object* v_xs_116_, lean_object* v_H_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; size_t v_sz_120_; size_t v___x_121_; lean_object* v___x_122_; 
v___f_118_ = lean_alloc_closure((void*)(l_Vector_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_118_, 0, v_f_115_);
v___x_119_ = ((lean_object*)(l_Vector_pmapImpl___redArg___closed__9));
v_sz_120_ = lean_array_size(v_xs_116_);
v___x_121_ = ((size_t)0ULL);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_119_, v___f_118_, v_sz_120_, v___x_121_, v_xs_116_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_n_125_, lean_object* v_P_126_, lean_object* v_f_127_, lean_object* v_xs_128_, lean_object* v_H_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Vector_pmapImpl(v_00_u03b1_123_, v_00_u03b2_124_, v_n_125_, v_P_126_, v_f_127_, v_xs_128_, v_H_129_);
lean_dec(v_n_125_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach___redArg(lean_object* v_xs_131_){
_start:
{
size_t v_sz_132_; size_t v___x_133_; lean_object* v___x_134_; 
v_sz_132_ = lean_array_size(v_xs_131_);
v___x_133_ = ((size_t)0ULL);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_132_, v___x_133_, v_xs_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach(lean_object* v_n_135_, lean_object* v_00_u03b1_136_, lean_object* v_p_137_, lean_object* v_xs_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Vector_unattach___redArg(v_xs_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach___boxed(lean_object* v_n_140_, lean_object* v_00_u03b1_141_, lean_object* v_p_142_, lean_object* v_xs_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Vector_unattach(v_n_140_, v_00_u03b1_141_, v_p_142_, v_xs_143_);
lean_dec(v_n_140_);
return v_res_144_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
