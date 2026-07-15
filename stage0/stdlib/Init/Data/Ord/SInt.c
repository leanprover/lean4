// Lean compiler output
// Module: Init.Data.Ord.SInt
// Imports: public import Init.Data.Order.Ord public import Init.Data.Order.ClassesExtra public import Init.Data.SInt.Basic import Init.Data.SInt.Lemmas import Init.Data.Order.Lemmas
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
uint8_t lean_int64_dec_lt(uint64_t, uint64_t);
uint8_t lean_int64_dec_eq(uint64_t, uint64_t);
uint8_t lean_int16_dec_lt(uint16_t, uint16_t);
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
uint8_t lean_int32_dec_lt(uint32_t, uint32_t);
uint8_t lean_int32_dec_eq(uint32_t, uint32_t);
uint8_t lean_int8_dec_lt(uint8_t, uint8_t);
uint8_t lean_int8_dec_eq(uint8_t, uint8_t);
uint8_t lean_isize_dec_lt(size_t, size_t);
uint8_t lean_isize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Int8_instOrd___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int8_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instOrd___closed__0 = (const lean_object*)&l_Int8_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Int8_instOrd = (const lean_object*)&l_Int8_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_Int16_instOrd___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int16_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instOrd___closed__0 = (const lean_object*)&l_Int16_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Int16_instOrd = (const lean_object*)&l_Int16_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_Int32_instOrd___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int32_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instOrd___closed__0 = (const lean_object*)&l_Int32_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Int32_instOrd = (const lean_object*)&l_Int32_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_Int64_instOrd___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int64_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instOrd___closed__0 = (const lean_object*)&l_Int64_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Int64_instOrd = (const lean_object*)&l_Int64_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_ISize_instOrd___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ISize_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instOrd___closed__0 = (const lean_object*)&l_ISize_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_ISize_instOrd = (const lean_object*)&l_ISize_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_Int8_instOrd___lam__0(uint8_t v_x_1_, uint8_t v_y_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_int8_dec_lt(v_x_1_, v_y_2_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; 
v___x_4_ = lean_int8_dec_eq(v_x_1_, v_y_2_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 2;
return v___x_5_;
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 1;
return v___x_6_;
}
}
else
{
uint8_t v___x_7_; 
v___x_7_ = 0;
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_instOrd___lam__0___boxed(lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v_x_boxed_10_; uint8_t v_y_boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_x_boxed_10_ = lean_unbox(v_x_8_);
v_y_boxed_11_ = lean_unbox(v_y_9_);
v_res_12_ = l_Int8_instOrd___lam__0(v_x_boxed_10_, v_y_boxed_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Int16_instOrd___lam__0(uint16_t v_x_16_, uint16_t v_y_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_int16_dec_lt(v_x_16_, v_y_17_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = lean_int16_dec_eq(v_x_16_, v_y_17_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = 2;
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_instOrd___lam__0___boxed(lean_object* v_x_23_, lean_object* v_y_24_){
_start:
{
uint16_t v_x_boxed_25_; uint16_t v_y_boxed_26_; uint8_t v_res_27_; lean_object* v_r_28_; 
v_x_boxed_25_ = lean_unbox(v_x_23_);
v_y_boxed_26_ = lean_unbox(v_y_24_);
v_res_27_ = l_Int16_instOrd___lam__0(v_x_boxed_25_, v_y_boxed_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Int32_instOrd___lam__0(uint32_t v_x_31_, uint32_t v_y_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = lean_int32_dec_lt(v_x_31_, v_y_32_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; 
v___x_34_ = lean_int32_dec_eq(v_x_31_, v_y_32_);
if (v___x_34_ == 0)
{
uint8_t v___x_35_; 
v___x_35_ = 2;
return v___x_35_;
}
else
{
uint8_t v___x_36_; 
v___x_36_ = 1;
return v___x_36_;
}
}
else
{
uint8_t v___x_37_; 
v___x_37_ = 0;
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_instOrd___lam__0___boxed(lean_object* v_x_38_, lean_object* v_y_39_){
_start:
{
uint32_t v_x_boxed_40_; uint32_t v_y_boxed_41_; uint8_t v_res_42_; lean_object* v_r_43_; 
v_x_boxed_40_ = lean_unbox_uint32(v_x_38_);
lean_dec(v_x_38_);
v_y_boxed_41_ = lean_unbox_uint32(v_y_39_);
lean_dec(v_y_39_);
v_res_42_ = l_Int32_instOrd___lam__0(v_x_boxed_40_, v_y_boxed_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_Int64_instOrd___lam__0(uint64_t v_x_46_, uint64_t v_y_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_int64_dec_lt(v_x_46_, v_y_47_);
if (v___x_48_ == 0)
{
uint8_t v___x_49_; 
v___x_49_ = lean_int64_dec_eq(v_x_46_, v_y_47_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = 2;
return v___x_50_;
}
else
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_instOrd___lam__0___boxed(lean_object* v_x_53_, lean_object* v_y_54_){
_start:
{
uint64_t v_x_boxed_55_; uint64_t v_y_boxed_56_; uint8_t v_res_57_; lean_object* v_r_58_; 
v_x_boxed_55_ = lean_unbox_uint64(v_x_53_);
lean_dec_ref(v_x_53_);
v_y_boxed_56_ = lean_unbox_uint64(v_y_54_);
lean_dec_ref(v_y_54_);
v_res_57_ = l_Int64_instOrd___lam__0(v_x_boxed_55_, v_y_boxed_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_ISize_instOrd___lam__0(size_t v_x_61_, size_t v_y_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lean_isize_dec_lt(v_x_61_, v_y_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; 
v___x_64_ = lean_isize_dec_eq(v_x_61_, v_y_62_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 2;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 1;
return v___x_66_;
}
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_instOrd___lam__0___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
size_t v_x_boxed_70_; size_t v_y_boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_boxed_70_ = lean_unbox_usize(v_x_68_);
lean_dec(v_x_68_);
v_y_boxed_71_ = lean_unbox_usize(v_y_69_);
lean_dec(v_y_69_);
v_res_72_ = l_ISize_instOrd___lam__0(v_x_boxed_70_, v_y_boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_SInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Ord_SInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_SInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Ord_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Ord_SInt(builtin);
}
#ifdef __cplusplus
}
#endif
