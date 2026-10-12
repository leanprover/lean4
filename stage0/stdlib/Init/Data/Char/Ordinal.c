// Lean compiler output
// Module: Init.Data.Char.Ordinal
// Imports: public import Init.Data.Fin.OverflowAware public import Init.Data.Function import Init.Data.Char.Lemmas import Init.Data.Char.Order import Init.Grind public import Init.Data.Char.Basic import Init.ByCases import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Internal.Linear import Init.Data.Nat.Simproc import Init.Data.Option.Lemmas import Init.Data.UInt.Lemmas
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
lean_object* l_Char_ordinal(uint32_t v_c_3_){
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
LEAN_EXPORT void l_Char_ordinal_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_3_ = stack[0].m_num;
lean_object* v_res_10_;
v_res_10_ = l_Char_ordinal(v_c_3_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Char_ordinal___boxed(lean_object* v_c_11_){
_start:
{
uint32_t v_c_boxed_12_; lean_object* v_res_13_; 
v_c_boxed_12_ = lean_unbox_uint32(v_c_11_);
lean_dec(v_c_11_);
v_res_13_ = l_Char_ordinal(v_c_boxed_12_);
return v_res_13_;
}
}
uint32_t l_Char_ofOrdinal(lean_object* v_f_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(55296u);
v___x_16_ = lean_nat_dec_lt(v_f_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; uint32_t v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(2048u);
v___x_18_ = lean_nat_add(v_f_14_, v___x_17_);
v___x_19_ = lean_uint32_of_nat(v___x_18_);
lean_dec(v___x_18_);
return v___x_19_;
}
else
{
uint32_t v___x_20_; 
v___x_20_ = lean_uint32_of_nat(v_f_14_);
return v___x_20_;
}
}
}
LEAN_EXPORT void l_Char_ofOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_14_ = stack[0].m_obj;
uint32_t v_res_21_;
v_res_21_ = l_Char_ofOrdinal(v_f_14_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Char_ofOrdinal___boxed(lean_object* v_f_22_){
_start:
{
uint32_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Char_ofOrdinal(v_f_22_);
lean_dec(v_f_22_);
v_r_24_ = lean_box_uint32(v_res_23_);
return v_r_24_;
}
}
static lean_object* _init_l_Char_succ_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_25_; lean_object* v___x_26_; 
v___x_25_ = 57344;
v___x_26_ = lean_box_uint32(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Char_succ_x3f___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = l_Char_succ_x3f___closed__0___boxed__const__1;
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
lean_object* l_Char_succ_x3f(uint32_t v_c_29_){
_start:
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 55295;
v___x_31_ = lean_uint32_dec_lt(v_c_29_, v___x_30_);
if (v___x_31_ == 0)
{
uint8_t v___x_32_; 
v___x_32_ = lean_uint32_dec_eq(v_c_29_, v___x_30_);
if (v___x_32_ == 0)
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 1114111;
v___x_34_ = lean_uint32_dec_lt(v_c_29_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
else
{
uint32_t v___x_36_; uint32_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = 1;
v___x_37_ = lean_uint32_add(v_c_29_, v___x_36_);
v___x_38_ = lean_box_uint32(v___x_37_);
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
else
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Char_succ_x3f___closed__0, &l_Char_succ_x3f___closed__0_once, _init_l_Char_succ_x3f___closed__0);
return v___x_40_;
}
}
else
{
uint32_t v___x_41_; uint32_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = 1;
v___x_42_ = lean_uint32_add(v_c_29_, v___x_41_);
v___x_43_ = lean_box_uint32(v___x_42_);
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT void l_Char_succ_x3f_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_29_ = stack[0].m_num;
lean_object* v_res_45_;
v_res_45_ = l_Char_succ_x3f(v_c_29_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Char_succ_x3f___boxed(lean_object* v_c_46_){
_start:
{
uint32_t v_c_boxed_47_; lean_object* v_res_48_; 
v_c_boxed_47_ = lean_unbox_uint32(v_c_46_);
lean_dec(v_c_46_);
v_res_48_ = l_Char_succ_x3f(v_c_boxed_47_);
return v_res_48_;
}
}
lean_object* l_Char_succMany_x3f(lean_object* v_m_49_, uint32_t v_c_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_51_ = lean_unsigned_to_nat(1112064u);
v___x_52_ = l_Char_ordinal(v_c_50_);
v___x_53_ = lean_nat_add(v___x_52_, v_m_49_);
lean_dec(v___x_52_);
v___x_54_ = lean_nat_dec_lt(v___x_53_, v___x_51_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec(v___x_53_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
uint32_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Char_ofOrdinal(v___x_53_);
lean_dec(v___x_53_);
v___x_57_ = lean_box_uint32(v___x_56_);
v___x_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT void l_Char_succMany_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_49_ = stack[0].m_obj;
uint32_t v_c_50_ = stack[1].m_num;
lean_object* v_res_59_;
v_res_59_ = l_Char_succMany_x3f(v_m_49_, v_c_50_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Char_succMany_x3f___boxed(lean_object* v_m_60_, lean_object* v_c_61_){
_start:
{
uint32_t v_c_boxed_62_; lean_object* v_res_63_; 
v_c_boxed_62_ = lean_unbox_uint32(v_c_61_);
lean_dec(v_c_61_);
v_res_63_ = l_Char_succMany_x3f(v_m_60_, v_c_boxed_62_);
lean_dec(v_m_60_);
return v_res_63_;
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
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Char_Ordinal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
