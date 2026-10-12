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
uint8_t l_Int8_instOrd___lam__0(uint8_t v_x_1_, uint8_t v_y_2_){
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
LEAN_EXPORT void l_Int8_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
uint8_t v_y_2_ = stack[1].m_num;
uint8_t v_res_8_;
v_res_8_ = l_Int8_instOrd___lam__0(v_x_1_, v_y_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Int8_instOrd___lam__0___boxed(lean_object* v_x_9_, lean_object* v_y_10_){
_start:
{
uint8_t v_x_boxed_11_; uint8_t v_y_boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_x_boxed_11_ = lean_unbox(v_x_9_);
v_y_boxed_12_ = lean_unbox(v_y_10_);
v_res_13_ = l_Int8_instOrd___lam__0(v_x_boxed_11_, v_y_boxed_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_Int16_instOrd___lam__0(uint16_t v_x_17_, uint16_t v_y_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_int16_dec_lt(v_x_17_, v_y_18_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = lean_int16_dec_eq(v_x_17_, v_y_18_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 2;
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 1;
return v___x_22_;
}
}
else
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
}
}
LEAN_EXPORT void l_Int16_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_17_ = stack[0].m_num;
uint16_t v_y_18_ = stack[1].m_num;
uint8_t v_res_24_;
v_res_24_ = l_Int16_instOrd___lam__0(v_x_17_, v_y_18_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_Int16_instOrd___lam__0___boxed(lean_object* v_x_25_, lean_object* v_y_26_){
_start:
{
uint16_t v_x_boxed_27_; uint16_t v_y_boxed_28_; uint8_t v_res_29_; lean_object* v_r_30_; 
v_x_boxed_27_ = lean_unbox(v_x_25_);
v_y_boxed_28_ = lean_unbox(v_y_26_);
v_res_29_ = l_Int16_instOrd___lam__0(v_x_boxed_27_, v_y_boxed_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
uint8_t l_Int32_instOrd___lam__0(uint32_t v_x_33_, uint32_t v_y_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_int32_dec_lt(v_x_33_, v_y_34_);
if (v___x_35_ == 0)
{
uint8_t v___x_36_; 
v___x_36_ = lean_int32_dec_eq(v_x_33_, v_y_34_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; 
v___x_37_ = 2;
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = 1;
return v___x_38_;
}
}
else
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
}
LEAN_EXPORT void l_Int32_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_33_ = stack[0].m_num;
uint32_t v_y_34_ = stack[1].m_num;
uint8_t v_res_40_;
v_res_40_ = l_Int32_instOrd___lam__0(v_x_33_, v_y_34_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Int32_instOrd___lam__0___boxed(lean_object* v_x_41_, lean_object* v_y_42_){
_start:
{
uint32_t v_x_boxed_43_; uint32_t v_y_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_x_boxed_43_ = lean_unbox_uint32(v_x_41_);
lean_dec(v_x_41_);
v_y_boxed_44_ = lean_unbox_uint32(v_y_42_);
lean_dec(v_y_42_);
v_res_45_ = l_Int32_instOrd___lam__0(v_x_boxed_43_, v_y_boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
uint8_t l_Int64_instOrd___lam__0(uint64_t v_x_49_, uint64_t v_y_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = lean_int64_dec_lt(v_x_49_, v_y_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = lean_int64_dec_eq(v_x_49_, v_y_50_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = 2;
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
}
}
LEAN_EXPORT void l_Int64_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_49_ = stack[0].m_num;
uint64_t v_y_50_ = stack[1].m_num;
uint8_t v_res_56_;
v_res_56_ = l_Int64_instOrd___lam__0(v_x_49_, v_y_50_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Int64_instOrd___lam__0___boxed(lean_object* v_x_57_, lean_object* v_y_58_){
_start:
{
uint64_t v_x_boxed_59_; uint64_t v_y_boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_x_boxed_59_ = lean_unbox_uint64(v_x_57_);
lean_dec_ref(v_x_57_);
v_y_boxed_60_ = lean_unbox_uint64(v_y_58_);
lean_dec_ref(v_y_58_);
v_res_61_ = l_Int64_instOrd___lam__0(v_x_boxed_59_, v_y_boxed_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
uint8_t l_ISize_instOrd___lam__0(size_t v_x_65_, size_t v_y_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_isize_dec_lt(v_x_65_, v_y_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = lean_isize_dec_eq(v_x_65_, v_y_66_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 2;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT void l_ISize_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_x_65_ = stack[0].m_num;
size_t v_y_66_ = stack[1].m_num;
uint8_t v_res_72_;
v_res_72_ = l_ISize_instOrd___lam__0(v_x_65_, v_y_66_);
stack->m_num = v_res_72_;
}
LEAN_EXPORT lean_object* l_ISize_instOrd___lam__0___boxed(lean_object* v_x_73_, lean_object* v_y_74_){
_start:
{
size_t v_x_boxed_75_; size_t v_y_boxed_76_; uint8_t v_res_77_; lean_object* v_r_78_; 
v_x_boxed_75_ = lean_unbox_usize(v_x_73_);
lean_dec(v_x_73_);
v_y_boxed_76_ = lean_unbox_usize(v_y_74_);
lean_dec(v_y_74_);
v_res_77_ = l_ISize_instOrd___lam__0(v_x_boxed_75_, v_y_boxed_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_SInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
