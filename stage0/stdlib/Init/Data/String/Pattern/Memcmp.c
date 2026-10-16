// Lean compiler output
// Module: Init.Data.String.Pattern.Memcmp
// Imports: public import Init.Data.String.Basic import Init.Data.String.Lemmas.Order import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_1_, lean_object* v_rhs_2_, lean_object* v_lstart_3_, lean_object* v_rstart_4_, lean_object* v_len_5_, lean_object* v_curr_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_curr_6_, v___x_7_);
v___x_9_ = lean_nat_dec_le(v___x_8_, v_len_5_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
lean_dec(v___x_8_);
lean_dec(v_curr_6_);
v___x_10_ = 1;
return v___x_10_;
}
else
{
lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; uint8_t v___x_15_; 
v___x_11_ = lean_nat_add(v_lstart_3_, v_curr_6_);
v___x_12_ = lean_string_get_byte_fast(v_lhs_1_, v___x_11_);
v___x_13_ = lean_nat_add(v_rstart_4_, v_curr_6_);
lean_dec(v_curr_6_);
v___x_14_ = lean_string_get_byte_fast(v_rhs_2_, v___x_13_);
v___x_15_ = lean_uint8_dec_eq(v___x_12_, v___x_14_);
if (v___x_15_ == 0)
{
lean_dec(v___x_8_);
return v___x_15_;
}
else
{
v_curr_6_ = v___x_8_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_17_, lean_object* v_rhs_18_, lean_object* v_lstart_19_, lean_object* v_rstart_20_, lean_object* v_len_21_, lean_object* v_curr_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_17_, v_rhs_18_, v_lstart_19_, v_rstart_20_, v_len_21_, v_curr_22_);
lean_dec(v_len_21_);
lean_dec(v_rstart_20_);
lean_dec(v_lstart_19_);
lean_dec_ref(v_rhs_18_);
lean_dec_ref(v_lhs_17_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_25_, lean_object* v_rhs_26_, lean_object* v_lstart_27_, lean_object* v_rstart_28_, lean_object* v_len_29_, lean_object* v_h1_30_, lean_object* v_h2_31_, lean_object* v_curr_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_25_, v_rhs_26_, v_lstart_27_, v_rstart_28_, v_len_29_, v_curr_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_34_, lean_object* v_rhs_35_, lean_object* v_lstart_36_, lean_object* v_rstart_37_, lean_object* v_len_38_, lean_object* v_h1_39_, lean_object* v_h2_40_, lean_object* v_curr_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l___private_Init_Data_String_Pattern_Memcmp_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_34_, v_rhs_35_, v_lstart_36_, v_rstart_37_, v_len_38_, v_h1_39_, v_h2_40_, v_curr_41_);
lean_dec(v_len_38_);
lean_dec(v_rstart_37_);
lean_dec(v_lstart_36_);
lean_dec_ref(v_rhs_35_);
lean_dec_ref(v_lhs_34_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_51_, lean_object* v_rhs_52_, lean_object* v_lstart_53_, lean_object* v_rstart_54_, lean_object* v_len_55_, lean_object* v_h1_56_, lean_object* v_h2_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = lean_string_memcmp(v_lhs_51_, v_rhs_52_, v_lstart_53_, v_rstart_54_, v_len_55_);
lean_dec(v_len_55_);
lean_dec(v_rstart_54_);
lean_dec(v_lstart_53_);
lean_dec_ref(v_rhs_52_);
lean_dec_ref(v_lhs_51_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_60_, lean_object* v_rhs_61_, lean_object* v_lstart_62_, lean_object* v_rstart_63_, lean_object* v_len_64_){
_start:
{
lean_object* v_str_65_; lean_object* v_startInclusive_66_; lean_object* v_str_67_; lean_object* v_startInclusive_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_str_65_ = lean_ctor_get(v_lhs_60_, 0);
v_startInclusive_66_ = lean_ctor_get(v_lhs_60_, 1);
v_str_67_ = lean_ctor_get(v_rhs_61_, 0);
v_startInclusive_68_ = lean_ctor_get(v_rhs_61_, 1);
v___x_69_ = lean_nat_add(v_startInclusive_66_, v_lstart_62_);
v___x_70_ = lean_nat_add(v_startInclusive_68_, v_rstart_63_);
v___x_71_ = lean_string_memcmp(v_str_65_, v_str_67_, v___x_69_, v___x_70_, v_len_64_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_72_, lean_object* v_rhs_73_, lean_object* v_lstart_74_, lean_object* v_rstart_75_, lean_object* v_len_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_72_, v_rhs_73_, v_lstart_74_, v_rstart_75_, v_len_76_);
lean_dec(v_len_76_);
lean_dec(v_rstart_75_);
lean_dec(v_lstart_74_);
lean_dec_ref(v_rhs_73_);
lean_dec_ref(v_lhs_72_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_79_, lean_object* v_rhs_80_, lean_object* v_lstart_81_, lean_object* v_rstart_82_, lean_object* v_len_83_, lean_object* v_h1_84_, lean_object* v_h2_85_){
_start:
{
lean_object* v_str_86_; lean_object* v_startInclusive_87_; lean_object* v_str_88_; lean_object* v_startInclusive_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_str_86_ = lean_ctor_get(v_lhs_79_, 0);
v_startInclusive_87_ = lean_ctor_get(v_lhs_79_, 1);
v_str_88_ = lean_ctor_get(v_rhs_80_, 0);
v_startInclusive_89_ = lean_ctor_get(v_rhs_80_, 1);
v___x_90_ = lean_nat_add(v_startInclusive_87_, v_lstart_81_);
v___x_91_ = lean_nat_add(v_startInclusive_89_, v_rstart_82_);
v___x_92_ = lean_string_memcmp(v_str_86_, v_str_88_, v___x_90_, v___x_91_, v_len_83_);
lean_dec(v___x_91_);
lean_dec(v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_93_, lean_object* v_rhs_94_, lean_object* v_lstart_95_, lean_object* v_rstart_96_, lean_object* v_len_97_, lean_object* v_h1_98_, lean_object* v_h2_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_93_, v_rhs_94_, v_lstart_95_, v_rstart_96_, v_len_97_, v_h1_98_, v_h2_99_);
lean_dec(v_len_97_);
lean_dec(v_rstart_96_);
lean_dec(v_lstart_95_);
lean_dec_ref(v_rhs_94_);
lean_dec_ref(v_lhs_93_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Pattern_Memcmp(builtin);
}
#ifdef __cplusplus
}
#endif
