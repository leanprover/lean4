// Lean compiler output
// Module: Init.Data.ByteArray.Lex
// Imports: public import Init.Data.Order.PackageFactories public import Init.Data.Order.Factories public import Init.Data.ByteArray.Lemmas public import Init.Data.Array.Lex.Lemmas public import Init.Data.Ord.Array public import Init.Data.Ord.UInt public import Init.Data.UInt.Package public import Init.Data.Array.Package public import Init.Data.Order.LemmasExtra
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
lean_object* l_ByteArray_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instLT;
LEAN_EXPORT lean_object* l_ByteArray_instLE;
uint8_t lean_byte_array_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_decidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_instDecidableLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instDecidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_instDecidableLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instDecidableLE___boxed(lean_object*, lean_object*);
uint8_t lean_byte_array_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instOrd___closed__0 = (const lean_object*)&l_ByteArray_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instOrd = (const lean_object*)&l_ByteArray_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lex_0__ByteArray_instTransNotLt;
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_instLinearOrderPackage___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instLinearOrderPackage___closed__0 = (const lean_object*)&l_ByteArray_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_ByteArray_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_instLinearOrderPackage___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instLinearOrderPackage___closed__1 = (const lean_object*)&l_ByteArray_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_ByteArray_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instLinearOrderPackage___closed__2 = (const lean_object*)&l_ByteArray_instLinearOrderPackage___closed__2_value;
static lean_once_cell_t l_ByteArray_instLinearOrderPackage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_instLinearOrderPackage___closed__3;
static lean_once_cell_t l_ByteArray_instLinearOrderPackage___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_instLinearOrderPackage___closed__4;
static lean_once_cell_t l_ByteArray_instLinearOrderPackage___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_instLinearOrderPackage___closed__5;
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage;
static lean_object* _init_l_ByteArray_instLT(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_ByteArray_instLE(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_ByteArray_decidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3_ = stack[0].m_obj;
lean_object* v_b_4_ = stack[1].m_obj;
uint8_t v_res_5_;
v_res_5_ = lean_byte_array_dec_lt(v_a_3_, v_b_4_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_ByteArray_decidableLT___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = lean_byte_array_dec_lt(v_a_6_, v_b_7_);
lean_dec_ref(v_b_7_);
lean_dec_ref(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
uint8_t l_ByteArray_instDecidableLT(lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_byte_array_dec_lt(v_a_10_, v_b_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l_ByteArray_instDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_10_ = stack[0].m_obj;
lean_object* v_b_11_ = stack[1].m_obj;
uint8_t v_res_13_;
v_res_13_ = l_ByteArray_instDecidableLT(v_a_10_, v_b_11_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableLT___boxed(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_ByteArray_instDecidableLT(v_a_14_, v_b_15_);
lean_dec_ref(v_b_15_);
lean_dec_ref(v_a_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l_ByteArray_instDecidableLE(lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_byte_array_dec_lt(v_b_19_, v_a_18_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
}
LEAN_EXPORT void l_ByteArray_instDecidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_18_ = stack[0].m_obj;
lean_object* v_b_19_ = stack[1].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_ByteArray_instDecidableLE(v_a_18_, v_b_19_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableLE___boxed(lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_ByteArray_instDecidableLE(v_a_24_, v_b_25_);
lean_dec_ref(v_b_25_);
lean_dec_ref(v_a_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT void l_ByteArray_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_28_ = stack[0].m_obj;
lean_object* v_b_29_ = stack[1].m_obj;
uint8_t v_res_30_;
v_res_30_ = lean_byte_array_compare(v_a_28_, v_b_29_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_ByteArray_compare___boxed(lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = lean_byte_array_compare(v_a_31_, v_b_32_);
lean_dec_ref(v_b_32_);
lean_dec_ref(v_a_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
static lean_object* _init_l___private_Init_Data_ByteArray_Lex_0__ByteArray_instTransNotLt(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__0(lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = l_ByteArray_instDecidableLE(v_a_38_, v_b_39_);
if (v___x_40_ == 0)
{
lean_inc_ref(v_b_39_);
return v_b_39_;
}
else
{
lean_inc_ref(v_a_38_);
return v_a_38_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__0___boxed(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_ByteArray_instLinearOrderPackage___lam__0(v_a_41_, v_b_42_);
lean_dec_ref(v_b_42_);
lean_dec_ref(v_a_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__1(lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_ByteArray_instDecidableLE(v_b_45_, v_a_44_);
if (v___x_46_ == 0)
{
lean_inc_ref(v_b_45_);
return v_b_45_;
}
else
{
lean_inc_ref(v_a_44_);
return v_a_44_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__1___boxed(lean_object* v_a_47_, lean_object* v_b_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_ByteArray_instLinearOrderPackage___lam__1(v_a_47_, v_b_48_);
lean_dec_ref(v_b_48_);
lean_dec_ref(v_a_47_);
return v_res_49_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v_this_54_; lean_object* v___x_55_; lean_object* v_this_56_; lean_object* v_this_57_; lean_object* v___x_58_; 
v___x_53_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableLT___boxed), 2, 0);
v_this_54_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableLE___boxed), 2, 0);
v___x_55_ = ((lean_object*)(l_ByteArray_instLinearOrderPackage___closed__2));
v_this_56_ = lean_box(0);
v_this_57_ = lean_box(0);
v___x_58_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_58_, 0, v_this_57_);
lean_ctor_set(v___x_58_, 1, v_this_56_);
lean_ctor_set(v___x_58_, 2, v___x_55_);
lean_ctor_set(v___x_58_, 3, v_this_54_);
lean_ctor_set(v___x_58_, 4, v___x_53_);
return v___x_58_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = ((lean_object*)(l_ByteArray_instOrd___closed__0));
v___x_60_ = lean_obj_once(&l_ByteArray_instLinearOrderPackage___closed__3, &l_ByteArray_instLinearOrderPackage___closed__3_once, _init_l_ByteArray_instLinearOrderPackage___closed__3);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage___closed__5(void){
_start:
{
lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___f_62_ = ((lean_object*)(l_ByteArray_instLinearOrderPackage___closed__1));
v___f_63_ = ((lean_object*)(l_ByteArray_instLinearOrderPackage___closed__0));
v___x_64_ = lean_obj_once(&l_ByteArray_instLinearOrderPackage___closed__4, &l_ByteArray_instLinearOrderPackage___closed__4_once, _init_l_ByteArray_instLinearOrderPackage___closed__4);
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___f_63_);
lean_ctor_set(v___x_65_, 2, v___f_62_);
return v___x_65_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_ByteArray_instLinearOrderPackage___closed__5, &l_ByteArray_instLinearOrderPackage___closed__5_once, _init_l_ByteArray_instLinearOrderPackage___closed__5);
return v___x_66_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Factories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Package(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Package(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Factories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ByteArray_instLT = _init_l_ByteArray_instLT();
lean_mark_persistent(l_ByteArray_instLT);
l_ByteArray_instLE = _init_l_ByteArray_instLE();
lean_mark_persistent(l_ByteArray_instLE);
l___private_Init_Data_ByteArray_Lex_0__ByteArray_instTransNotLt = _init_l___private_Init_Data_ByteArray_Lex_0__ByteArray_instTransNotLt();
l_ByteArray_instLinearOrderPackage = _init_l_ByteArray_instLinearOrderPackage();
lean_mark_persistent(l_ByteArray_instLinearOrderPackage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ByteArray_Lex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Factories(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Package(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Package(uint8_t builtin);
lean_object* initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Lex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Factories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ByteArray_Lex(builtin);
}
#ifdef __cplusplus
}
#endif
