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
LEAN_EXPORT lean_object* l_ByteArray_decidableLT___boxed(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lean_byte_array_dec_lt(v_a_5_, v_b_6_);
lean_dec_ref(v_b_6_);
lean_dec_ref(v_a_5_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instDecidableLT(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = lean_byte_array_dec_lt(v_a_9_, v_b_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableLT___boxed(lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_ByteArray_instDecidableLT(v_a_12_, v_b_13_);
lean_dec_ref(v_b_13_);
lean_dec_ref(v_a_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instDecidableLE(lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_byte_array_dec_lt(v_b_17_, v_a_16_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 1;
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableLE___boxed(lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_ByteArray_instDecidableLE(v_a_21_, v_b_22_);
lean_dec_ref(v_b_22_);
lean_dec_ref(v_a_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_compare___boxed(lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lean_byte_array_compare(v_a_27_, v_b_28_);
lean_dec_ref(v_b_28_);
lean_dec_ref(v_a_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
static lean_object* _init_l___private_Init_Data_ByteArray_Lex_0__ByteArray_instTransNotLt(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__0(lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_ByteArray_instDecidableLE(v_a_34_, v_b_35_);
if (v___x_36_ == 0)
{
lean_inc_ref(v_b_35_);
return v_b_35_;
}
else
{
lean_inc_ref(v_a_34_);
return v_a_34_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__0___boxed(lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_ByteArray_instLinearOrderPackage___lam__0(v_a_37_, v_b_38_);
lean_dec_ref(v_b_38_);
lean_dec_ref(v_a_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__1(lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = l_ByteArray_instDecidableLE(v_b_41_, v_a_40_);
if (v___x_42_ == 0)
{
lean_inc_ref(v_b_41_);
return v_b_41_;
}
else
{
lean_inc_ref(v_a_40_);
return v_a_40_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_instLinearOrderPackage___lam__1___boxed(lean_object* v_a_43_, lean_object* v_b_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_ByteArray_instLinearOrderPackage___lam__1(v_a_43_, v_b_44_);
lean_dec_ref(v_b_44_);
lean_dec_ref(v_a_43_);
return v_res_45_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage___closed__3(void){
_start:
{
lean_object* v___x_49_; lean_object* v_this_50_; lean_object* v___x_51_; lean_object* v_this_52_; lean_object* v_this_53_; lean_object* v___x_54_; 
v___x_49_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableLT___boxed), 2, 0);
v_this_50_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableLE___boxed), 2, 0);
v___x_51_ = ((lean_object*)(l_ByteArray_instLinearOrderPackage___closed__2));
v_this_52_ = lean_box(0);
v_this_53_ = lean_box(0);
v___x_54_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_54_, 0, v_this_53_);
lean_ctor_set(v___x_54_, 1, v_this_52_);
lean_ctor_set(v___x_54_, 2, v___x_51_);
lean_ctor_set(v___x_54_, 3, v_this_50_);
lean_ctor_set(v___x_54_, 4, v___x_49_);
return v___x_54_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage___closed__4(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((lean_object*)(l_ByteArray_instOrd___closed__0));
v___x_56_ = lean_obj_once(&l_ByteArray_instLinearOrderPackage___closed__3, &l_ByteArray_instLinearOrderPackage___closed__3_once, _init_l_ByteArray_instLinearOrderPackage___closed__3);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage___closed__5(void){
_start:
{
lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___f_58_ = ((lean_object*)(l_ByteArray_instLinearOrderPackage___closed__1));
v___f_59_ = ((lean_object*)(l_ByteArray_instLinearOrderPackage___closed__0));
v___x_60_ = lean_obj_once(&l_ByteArray_instLinearOrderPackage___closed__4, &l_ByteArray_instLinearOrderPackage___closed__4_once, _init_l_ByteArray_instLinearOrderPackage___closed__4);
v___x_61_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___f_59_);
lean_ctor_set(v___x_61_, 2, v___f_58_);
return v___x_61_;
}
}
static lean_object* _init_l_ByteArray_instLinearOrderPackage(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_ByteArray_instLinearOrderPackage___closed__5, &l_ByteArray_instLinearOrderPackage___closed__5_once, _init_l_ByteArray_instLinearOrderPackage___closed__5);
return v___x_62_;
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
