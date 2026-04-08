// Lean compiler output
// Module: Init.Data.Char.Ordinal
// Imports: public import Init.Data.Fin.OverflowAware public import Init.Data.Function import Init.Data.Char.Lemmas import Init.Data.Char.Order import Init.Grind public import Init.Data.Char.Basic import Init.ByCases import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Nat.Simproc import Init.Data.Option.Lemmas import Init.Data.UInt.Lemmas
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
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Char_numSurrogates;
LEAN_EXPORT lean_object* l_Char_numCodePoints;
LEAN_EXPORT lean_object* l_Char_ordinal(uint32_t);
LEAN_EXPORT lean_object* l_Char_ordinal___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Char_ofOrdinal(lean_object*);
LEAN_EXPORT lean_object* l_Char_ofOrdinal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_succ_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_Char_succ_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_succ_x3f___closed__0;
LEAN_EXPORT lean_object* l_Char_succ_x3f(uint32_t);
LEAN_EXPORT lean_object* l_Char_succ_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_succMany_x3f(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Char_succMany_x3f___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Char_numSurrogates(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(2048u);
return v___x_1_;
}
}
static lean_object* _init_l_Char_numCodePoints(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(1112064u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Char_ordinal(uint32_t v_c_3_){
_start:
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 55296;
v___x_5_ = lean_uint32_dec_lt(v_c_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_uint32_to_nat(v_c_3_);
v___x_7_ = lean_unsigned_to_nat(2048u);
v___x_8_ = lean_nat_sub(v___x_6_, v___x_7_);
lean_dec(v___x_6_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
v___x_9_ = lean_uint32_to_nat(v_c_3_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Char_ordinal___boxed(lean_object* v_c_10_){
_start:
{
uint32_t v_c_boxed_11_; lean_object* v_res_12_; 
v_c_boxed_11_ = lean_unbox_uint32(v_c_10_);
lean_dec(v_c_10_);
v_res_12_ = l_Char_ordinal(v_c_boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT uint32_t l_Char_ofOrdinal(lean_object* v_f_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(55296u);
v___x_15_ = lean_nat_dec_lt(v_f_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; uint32_t v___x_18_; 
v___x_16_ = lean_unsigned_to_nat(2048u);
v___x_17_ = lean_nat_add(v_f_13_, v___x_16_);
v___x_18_ = lean_uint32_of_nat(v___x_17_);
lean_dec(v___x_17_);
return v___x_18_;
}
else
{
uint32_t v___x_19_; 
v___x_19_ = lean_uint32_of_nat(v_f_13_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Char_ofOrdinal___boxed(lean_object* v_f_20_){
_start:
{
uint32_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Char_ofOrdinal(v_f_20_);
lean_dec(v_f_20_);
v_r_22_ = lean_box_uint32(v_res_21_);
return v_r_22_;
}
}
static lean_object* _init_l_Char_succ_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_23_; lean_object* v___x_24_; 
v___x_23_ = 57344;
v___x_24_ = lean_box_uint32(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Char_succ_x3f___closed__0(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = l_Char_succ_x3f___closed__0___boxed__const__1;
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Char_succ_x3f(uint32_t v_c_27_){
_start:
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 55295;
v___x_29_ = lean_uint32_dec_lt(v_c_27_, v___x_28_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; 
v___x_30_ = lean_uint32_dec_eq(v_c_27_, v___x_28_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 1114111;
v___x_32_ = lean_uint32_dec_lt(v_c_27_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
else
{
uint32_t v___x_34_; uint32_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_34_ = 1;
v___x_35_ = lean_uint32_add(v_c_27_, v___x_34_);
v___x_36_ = lean_box_uint32(v___x_35_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Char_succ_x3f___closed__0, &l_Char_succ_x3f___closed__0_once, _init_l_Char_succ_x3f___closed__0);
return v___x_38_;
}
}
else
{
uint32_t v___x_39_; uint32_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = 1;
v___x_40_ = lean_uint32_add(v_c_27_, v___x_39_);
v___x_41_ = lean_box_uint32(v___x_40_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Char_succ_x3f___boxed(lean_object* v_c_43_){
_start:
{
uint32_t v_c_boxed_44_; lean_object* v_res_45_; 
v_c_boxed_44_ = lean_unbox_uint32(v_c_43_);
lean_dec(v_c_43_);
v_res_45_ = l_Char_succ_x3f(v_c_boxed_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Char_succMany_x3f(lean_object* v_m_46_, uint32_t v_c_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_48_ = lean_unsigned_to_nat(1112064u);
v___x_49_ = l_Char_ordinal(v_c_47_);
v___x_50_ = lean_nat_add(v___x_49_, v_m_46_);
lean_dec(v___x_49_);
v___x_51_ = lean_nat_dec_lt(v___x_50_, v___x_48_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec(v___x_50_);
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
uint32_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = l_Char_ofOrdinal(v___x_50_);
lean_dec(v___x_50_);
v___x_54_ = lean_box_uint32(v___x_53_);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Char_succMany_x3f___boxed(lean_object* v_m_56_, lean_object* v_c_57_){
_start:
{
uint32_t v_c_boxed_58_; lean_object* v_res_59_; 
v_c_boxed_58_ = lean_unbox_uint32(v_c_57_);
lean_dec(v_c_57_);
v_res_59_ = l_Char_succMany_x3f(v_m_56_, v_c_boxed_58_);
lean_dec(v_m_56_);
return v_res_59_;
}
}
lean_object* runtime_initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Char_Ordinal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_numSurrogates = _init_l_Char_numSurrogates();
lean_mark_persistent(l_Char_numSurrogates);
l_Char_numCodePoints = _init_l_Char_numCodePoints();
lean_mark_persistent(l_Char_numCodePoints);
l_Char_succ_x3f___closed__0___boxed__const__1 = _init_l_Char_succ_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_Char_succ_x3f___closed__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Char_Ordinal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Ordinal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Ordinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Char_Ordinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Char_Ordinal(builtin);
}
#ifdef __cplusplus
}
#endif
