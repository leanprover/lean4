// Lean compiler output
// Module: Init.GrindInstances.ToInt
// Imports: import all Init.Grind.ToInt public import Init.Data.SInt.Basic public import Init.Grind.ToInt import Init.Data.BitVec.Bootstrap import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.SInt.Lemmas import Init.Data.UInt.Lemmas import Init.System.Platform
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
lean_object* l_Int32_toInt___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Int16_toInt___boxed(lean_object*);
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* l_ISize_toInt___boxed(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Int64_toInt___boxed(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_cast(lean_object*, lean_object*, lean_object*);
lean_object* l_Int8_toInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntIntIi___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Grind_instToIntIntIi___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntIntIi___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntIntIi = (const lean_object*)&l_Lean_Grind_instToIntIntIi___closed__0_value;
static lean_once_cell_t l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_instToIntNatCiOfNatInt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntNatCiOfNatInt;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUSizeUintNumBits = (const lean_object*)&l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value;
static const lean_closure_object l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt8SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value;
static const lean_closure_object l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt16SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value;
static const lean_closure_object l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt32SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value;
static const lean_closure_object l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt64SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntISizeSintNumBits___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntISizeSintNumBits = (const lean_object*)&l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value;
static lean_object* _init_l_Lean_Grind_instToIntNatCiOfNatInt___closed__0(void){
_start:
{
lean_object* v___f_3_; lean_object* v___x_4_; 
v___f_3_ = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
v___x_4_ = lean_alloc_closure((void*)(l_Nat_cast), 3, 2);
lean_closure_set(v___x_4_, 0, lean_box(0));
lean_closure_set(v___x_4_, 1, v___f_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Grind_instToIntNatCiOfNatInt(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Grind_instToIntNatCiOfNatInt___closed__0, &l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_once, _init_l_Lean_Grind_instToIntNatCiOfNatInt___closed__0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast(lean_object* v_n_6_){
_start:
{
lean_object* v___f_7_; 
v___f_7_ = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast___boxed(lean_object* v_n_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Grind_instToIntFinCoOfNatIntCast(v_n_8_);
lean_dec(v_n_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(uint8_t v_x_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_uint8_to_nat(v_x_10_);
v___x_12_ = lean_nat_to_int(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_boxed_14_; lean_object* v_res_15_; 
v_x_boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(v_x_boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(uint16_t v_x_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_uint16_to_nat(v_x_18_);
v___x_20_ = lean_nat_to_int(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed(lean_object* v_x_21_){
_start:
{
uint16_t v_x_boxed_22_; lean_object* v_res_23_; 
v_x_boxed_22_ = lean_unbox(v_x_21_);
v_res_23_ = l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(v_x_boxed_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(uint32_t v_x_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_uint32_to_nat(v_x_26_);
v___x_28_ = lean_nat_to_int(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed(lean_object* v_x_29_){
_start:
{
uint32_t v_x_boxed_30_; lean_object* v_res_31_; 
v_x_boxed_30_ = lean_unbox_uint32(v_x_29_);
lean_dec(v_x_29_);
v_res_31_ = l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(v_x_boxed_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(uint64_t v_x_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_uint64_to_nat(v_x_34_);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed(lean_object* v_x_37_){
_start:
{
uint64_t v_x_boxed_38_; lean_object* v_res_39_; 
v_x_boxed_38_ = lean_unbox_uint64(v_x_37_);
lean_dec_ref(v_x_37_);
v_res_39_ = l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(v_x_boxed_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(size_t v_x_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_usize_to_nat(v_x_42_);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed(lean_object* v_x_45_){
_start:
{
size_t v_x_boxed_46_; lean_object* v_res_47_; 
v_x_boxed_46_ = lean_unbox_usize(v_x_45_);
lean_dec(v_x_45_);
v_res_47_ = l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(v_x_boxed_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint(lean_object* v_v_58_){
_start:
{
lean_object* v___f_59_; 
v___f_59_ = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint___boxed(lean_object* v_v_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Grind_instToIntBitVecUint(v_v_60_);
lean_dec(v_v_60_);
return v_res_61_;
}
}
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instToIntNatCiOfNatInt = _init_l_Lean_Grind_instToIntNatCiOfNatInt();
lean_mark_persistent(l_Lean_Grind_instToIntNatCiOfNatInt);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GrindInstances_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GrindInstances_ToInt(builtin);
}
#ifdef __cplusplus
}
#endif
