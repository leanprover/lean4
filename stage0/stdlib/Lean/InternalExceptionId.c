// Lean compiler output
// Module: Lean.InternalExceptionId
// Imports: public import Init.System.IO import Init.Data.ToString.Name import Init.Data.ToString.Macro
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedInternalExceptionId_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInternalExceptionId;
LEAN_EXPORT uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqInternalExceptionId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqInternalExceptionId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqInternalExceptionId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqInternalExceptionId___closed__0 = (const lean_object*)&l_Lean_instBEqInternalExceptionId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqInternalExceptionId = (const lean_object*)&l_Lean_instBEqInternalExceptionId___closed__0_value;
static const lean_array_object l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_internalExceptionsRef;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_registerInternalExceptionId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid internal exception id, '"};
static const lean_object* l_Lean_registerInternalExceptionId___closed__0 = (const lean_object*)&l_Lean_registerInternalExceptionId___closed__0_value;
static const lean_string_object l_Lean_registerInternalExceptionId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "' has already been used"};
static const lean_object* l_Lean_registerInternalExceptionId___closed__1 = (const lean_object*)&l_Lean_registerInternalExceptionId___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_InternalExceptionId_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_InternalExceptionId_toString___closed__0 = (const lean_object*)&l_Lean_InternalExceptionId_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_toString(lean_object*);
static const lean_string_object l_Lean_InternalExceptionId_getName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "invalid internal exception id"};
static const lean_object* l_Lean_InternalExceptionId_getName___closed__0 = (const lean_object*)&l_Lean_InternalExceptionId_getName___closed__0_value;
static lean_once_cell_t l_Lean_InternalExceptionId_getName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_InternalExceptionId_getName___closed__1;
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedInternalExceptionId_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(0u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_instInhabitedInternalExceptionId(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_eq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_instBEqInternalExceptionId_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
lean_object* v_x_4_ = stack[1].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Lean_instBEqInternalExceptionId_beq(v_x_3_, v_x_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqInternalExceptionId_beq___boxed(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Lean_instBEqInternalExceptionId_beq(v_x_7_, v_x_8_);
lean_dec(v_x_8_);
lean_dec(v_x_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
lean_object* l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = ((lean_object*)(l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_));
v___x_17_ = lean_st_mk_ref(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_19_;
v_res_19_ = l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2____boxed(lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
return v_res_21_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(lean_object* v_a_22_, lean_object* v_as_23_, size_t v_i_24_, size_t v_stop_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_usize_dec_eq(v_i_24_, v_stop_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_array_uget_borrowed(v_as_23_, v_i_24_);
v___x_28_ = lean_name_eq(v_a_22_, v___x_27_);
if (v___x_28_ == 0)
{
size_t v___x_29_; size_t v___x_30_; 
v___x_29_ = ((size_t)1ULL);
v___x_30_ = lean_usize_add(v_i_24_, v___x_29_);
v_i_24_ = v___x_30_;
goto _start;
}
else
{
return v___x_28_;
}
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 0;
return v___x_32_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_22_ = stack[0].m_obj;
lean_object* v_as_23_ = stack[1].m_obj;
size_t v_i_24_ = stack[2].m_num;
size_t v_stop_25_ = stack[3].m_num;
uint8_t v_res_33_;
v_res_33_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(v_a_22_, v_as_23_, v_i_24_, v_stop_25_);
stack->m_num = v_res_33_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0___boxed(lean_object* v_a_34_, lean_object* v_as_35_, lean_object* v_i_36_, lean_object* v_stop_37_){
_start:
{
size_t v_i_boxed_38_; size_t v_stop_boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v_i_boxed_38_ = lean_unbox_usize(v_i_36_);
lean_dec(v_i_36_);
v_stop_boxed_39_ = lean_unbox_usize(v_stop_37_);
lean_dec(v_stop_37_);
v_res_40_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(v_a_34_, v_as_35_, v_i_boxed_38_, v_stop_boxed_39_);
lean_dec_ref(v_as_35_);
lean_dec(v_a_34_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
uint8_t l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(lean_object* v_as_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_array_get_size(v_as_42_);
v___x_46_ = lean_nat_dec_lt(v___x_44_, v___x_45_);
if (v___x_46_ == 0)
{
return v___x_46_;
}
else
{
if (v___x_46_ == 0)
{
return v___x_46_;
}
else
{
size_t v___x_47_; size_t v___x_48_; uint8_t v___x_49_; 
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_45_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(v_a_43_, v_as_42_, v___x_47_, v___x_48_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_42_ = stack[0].m_obj;
lean_object* v_a_43_ = stack[1].m_obj;
uint8_t v_res_50_;
v_res_50_ = l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(v_as_42_, v_a_43_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0___boxed(lean_object* v_as_51_, lean_object* v_a_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(v_as_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_as_51_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
lean_object* l_Lean_registerInternalExceptionId(lean_object* v_name_57_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_59_ = l_Lean_internalExceptionsRef;
v___x_60_ = lean_st_ref_get(v___x_59_);
v___x_61_ = l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(v___x_60_, v_name_57_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = lean_array_get_size(v___x_60_);
lean_dec(v___x_60_);
v___x_63_ = lean_st_ref_take(v___x_59_);
v___x_64_ = lean_array_push(v___x_63_, v_name_57_);
v___x_65_ = lean_st_ref_put(v___x_59_, v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_62_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v___x_60_);
v___x_67_ = ((lean_object*)(l_Lean_registerInternalExceptionId___closed__0));
v___x_68_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_57_, v___x_61_);
v___x_69_ = lean_string_append(v___x_67_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_70_ = ((lean_object*)(l_Lean_registerInternalExceptionId___closed__1));
v___x_71_ = lean_string_append(v___x_69_, v___x_70_);
v___x_72_ = lean_mk_io_user_error(v___x_71_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT void l_Lean_registerInternalExceptionId_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_57_ = stack[0].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_registerInternalExceptionId(v_name_57_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId___boxed(lean_object* v_name_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_registerInternalExceptionId(v_name_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_toString(lean_object* v_id_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l_Lean_InternalExceptionId_toString___closed__0));
v___x_81_ = l_Nat_reprFast(v_id_79_);
v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
lean_dec_ref(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_getName___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(l_Lean_InternalExceptionId_getName___closed__0));
v___x_85_ = lean_mk_io_user_error(v___x_84_);
return v___x_85_;
}
}
lean_object* l_Lean_InternalExceptionId_getName(lean_object* v_id_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = l_Lean_internalExceptionsRef;
v___x_89_ = lean_st_ref_get(v___x_88_);
v___x_90_ = lean_array_get_size(v___x_89_);
v___x_91_ = lean_nat_dec_lt(v_id_86_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v___x_89_);
v___x_92_ = lean_obj_once(&l_Lean_InternalExceptionId_getName___closed__1, &l_Lean_InternalExceptionId_getName___closed__1_once, _init_l_Lean_InternalExceptionId_getName___closed__1);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_array_fget(v___x_89_, v_id_86_);
lean_dec(v___x_89_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT void l_Lean_InternalExceptionId_getName_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_86_ = stack[0].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_InternalExceptionId_getName(v_id_86_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object* v_id_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_InternalExceptionId_getName(v_id_97_);
lean_dec(v_id_97_);
return v_res_99_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_InternalExceptionId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedInternalExceptionId_default = _init_l_Lean_instInhabitedInternalExceptionId_default();
lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId_default);
l_Lean_instInhabitedInternalExceptionId = _init_l_Lean_instInhabitedInternalExceptionId();
lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId);
res = l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_internalExceptionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internalExceptionsRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_InternalExceptionId(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_InternalExceptionId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_InternalExceptionId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_InternalExceptionId(builtin);
}
#ifdef __cplusplus
}
#endif
