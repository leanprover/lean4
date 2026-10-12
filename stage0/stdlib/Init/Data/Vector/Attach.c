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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(lean_object* v_f_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_bs_4_ = stack[3].m_obj;
lean_object* v_res_14_;
v_res_14_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_1_, v_sz_2_, v_i_3_, v_bs_4_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg___boxed(lean_object* v_f_15_, lean_object* v_sz_16_, lean_object* v_i_17_, lean_object* v_bs_18_){
_start:
{
size_t v_sz_boxed_19_; size_t v_i_boxed_20_; lean_object* v_res_21_; 
v_sz_boxed_19_ = lean_unbox_usize(v_sz_16_);
lean_dec(v_sz_16_);
v_i_boxed_20_ = lean_unbox_usize(v_i_17_);
lean_dec(v_i_17_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_15_, v_sz_boxed_19_, v_i_boxed_20_, v_bs_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmap___redArg(lean_object* v_f_22_, lean_object* v_xs_23_){
_start:
{
size_t v_sz_24_; size_t v___x_25_; lean_object* v___x_26_; 
v_sz_24_ = lean_array_size(v_xs_23_);
v___x_25_ = ((size_t)0ULL);
v___x_26_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_22_, v_sz_24_, v___x_25_, v_xs_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmap(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_n_29_, lean_object* v_P_30_, lean_object* v_f_31_, lean_object* v_xs_32_, lean_object* v_H_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Vector_pmap___redArg(v_f_31_, v_xs_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmap___boxed(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_n_37_, lean_object* v_P_38_, lean_object* v_f_39_, lean_object* v_xs_40_, lean_object* v_H_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Vector_pmap(v_00_u03b1_35_, v_00_u03b2_36_, v_n_37_, v_P_38_, v_f_39_, v_xs_40_, v_H_41_);
lean_dec(v_n_37_);
return v_res_42_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_f_45_, size_t v_sz_46_, size_t v_i_47_, lean_object* v_bs_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_45_, v_sz_46_, v_i_47_, v_bs_48_);
return v___x_49_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_45_ = stack[2].m_obj;
size_t v_sz_46_ = stack[3].m_num;
size_t v_i_47_ = stack[4].m_num;
lean_object* v_bs_48_ = stack[5].m_obj;
lean_object* v_res_50_;
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(lean_box(0), lean_box(0), v_f_45_, v_sz_46_, v_i_47_, v_bs_48_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___boxed(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_f_53_, lean_object* v_sz_54_, lean_object* v_i_55_, lean_object* v_bs_56_){
_start:
{
size_t v_sz_boxed_57_; size_t v_i_boxed_58_; lean_object* v_res_59_; 
v_sz_boxed_57_ = lean_unbox_usize(v_sz_54_);
lean_dec(v_sz_54_);
v_i_boxed_58_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_res_59_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(v_00_u03b1_51_, v_00_u03b2_52_, v_f_53_, v_sz_boxed_57_, v_i_boxed_58_, v_bs_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(lean_object* v_xs_60_){
_start:
{
lean_inc_ref(v_xs_60_);
return v_xs_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg___boxed(lean_object* v_xs_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(v_xs_61_);
lean_dec_ref(v_xs_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(lean_object* v_00_u03b1_63_, lean_object* v_n_64_, lean_object* v_xs_65_, lean_object* v_P_66_, lean_object* v_x_67_){
_start:
{
lean_inc_ref(v_xs_65_);
return v_xs_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___boxed(lean_object* v_00_u03b1_68_, lean_object* v_n_69_, lean_object* v_xs_70_, lean_object* v_P_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(v_00_u03b1_68_, v_n_69_, v_xs_70_, v_P_71_, v_x_72_);
lean_dec_ref(v_xs_70_);
lean_dec(v_n_69_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___redArg(lean_object* v_xs_74_){
_start:
{
lean_inc_ref(v_xs_74_);
return v_xs_74_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___redArg___boxed(lean_object* v_xs_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Vector_attach___redArg(v_xs_75_);
lean_dec_ref(v_xs_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach(lean_object* v_00_u03b1_77_, lean_object* v_n_78_, lean_object* v_xs_79_){
_start:
{
lean_inc_ref(v_xs_79_);
return v_xs_79_;
}
}
LEAN_EXPORT lean_object* l_Vector_attach___boxed(lean_object* v_00_u03b1_80_, lean_object* v_n_81_, lean_object* v_xs_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Vector_attach(v_00_u03b1_80_, v_n_81_, v_xs_82_);
lean_dec_ref(v_xs_82_);
lean_dec(v_n_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg___lam__0(lean_object* v_f_84_, lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_apply_2(v_f_84_, v_x_85_, lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___redArg(lean_object* v_f_106_, lean_object* v_xs_107_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; size_t v_sz_110_; size_t v___x_111_; lean_object* v___x_112_; 
v___f_108_ = lean_alloc_closure((void*)(l_Vector_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_108_, 0, v_f_106_);
v___x_109_ = ((lean_object*)(l_Vector_pmapImpl___redArg___closed__9));
v_sz_110_ = lean_array_size(v_xs_107_);
v___x_111_ = ((size_t)0ULL);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_109_, v___f_108_, v_sz_110_, v___x_111_, v_xs_107_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_n_115_, lean_object* v_P_116_, lean_object* v_f_117_, lean_object* v_xs_118_, lean_object* v_H_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; size_t v_sz_122_; size_t v___x_123_; lean_object* v___x_124_; 
v___f_120_ = lean_alloc_closure((void*)(l_Vector_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_120_, 0, v_f_117_);
v___x_121_ = ((lean_object*)(l_Vector_pmapImpl___redArg___closed__9));
v_sz_122_ = lean_array_size(v_xs_118_);
v___x_123_ = ((size_t)0ULL);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_121_, v___f_120_, v_sz_122_, v___x_123_, v_xs_118_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Vector_pmapImpl___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_n_127_, lean_object* v_P_128_, lean_object* v_f_129_, lean_object* v_xs_130_, lean_object* v_H_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Vector_pmapImpl(v_00_u03b1_125_, v_00_u03b2_126_, v_n_127_, v_P_128_, v_f_129_, v_xs_130_, v_H_131_);
lean_dec(v_n_127_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach___redArg(lean_object* v_xs_133_){
_start:
{
size_t v_sz_134_; size_t v___x_135_; lean_object* v___x_136_; 
v_sz_134_ = lean_array_size(v_xs_133_);
v___x_135_ = ((size_t)0ULL);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_134_, v___x_135_, v_xs_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach(lean_object* v_n_137_, lean_object* v_00_u03b1_138_, lean_object* v_p_139_, lean_object* v_xs_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Vector_unattach___redArg(v_xs_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Vector_unattach___boxed(lean_object* v_n_142_, lean_object* v_00_u03b1_143_, lean_object* v_p_144_, lean_object* v_xs_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Vector_unattach(v_n_142_, v_00_u03b1_143_, v_p_144_, v_xs_145_);
lean_dec(v_n_142_);
return v_res_146_;
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
