// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Char
// Imports: public import Init.Data.Char.Ordinal public import Init.Data.Range.Polymorphic.Fin import Init.Data.Range.Polymorphic.Map import Init.Data.Char.Order import Init.Data.Fin.Lemmas import Init.Data.Option.Lemmas
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
lean_object* l_Char_succMany_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Char_succ_x3f___boxed(lean_object*);
lean_object* l_Char_ordinal(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Char_ordinal___boxed(lean_object*);
static const lean_closure_object l_Char_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_succ_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instUpwardEnumerable___closed__0 = (const lean_object*)&l_Char_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_Char_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_succMany_x3f___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instUpwardEnumerable___closed__1 = (const lean_object*)&l_Char_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_Char_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Char_instUpwardEnumerable___closed__0_value),((lean_object*)&l_Char_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_Char_instUpwardEnumerable___closed__2 = (const lean_object*)&l_Char_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_Char_instUpwardEnumerable = (const lean_object*)&l_Char_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Char_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instHasSize___closed__0 = (const lean_object*)&l_Char_instHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Char_instHasSize = (const lean_object*)&l_Char_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Char_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instHasSize__1___closed__0 = (const lean_object*)&l_Char_instHasSize__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Char_instHasSize__1 = (const lean_object*)&l_Char_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_Char_instHasSize__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instHasSize__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instHasSize__2___closed__0 = (const lean_object*)&l_Char_instHasSize__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Char_instHasSize__2 = (const lean_object*)&l_Char_instHasSize__2___closed__0_value;
LEAN_EXPORT lean_object* l_Char_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_Char_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l_Char_instLeast_x3f;
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_ordinal___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Data_Range_Polymorphic_Char_0__Char_map = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value;
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0(uint32_t v_lo_7_, uint32_t v_hi_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_9_ = l_Char_ordinal(v_lo_7_);
v___x_10_ = l_Char_ordinal(v_hi_8_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v___x_10_, v___x_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_nat_sub(v___x_12_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0___boxed(lean_object* v_lo_14_, lean_object* v_hi_15_){
_start:
{
uint32_t v_lo_boxed_16_; uint32_t v_hi_boxed_17_; lean_object* v_res_18_; 
v_lo_boxed_16_ = lean_unbox_uint32(v_lo_14_);
lean_dec(v_lo_14_);
v_hi_boxed_17_ = lean_unbox_uint32(v_hi_15_);
lean_dec(v_hi_15_);
v_res_18_ = l_Char_instHasSize___lam__0(v_lo_boxed_16_, v_hi_boxed_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0(uint32_t v_lo_21_, uint32_t v_hi_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_23_ = l_Char_ordinal(v_lo_21_);
v___x_24_ = l_Char_ordinal(v_hi_22_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_nat_sub(v___x_26_, v___x_23_);
lean_dec(v___x_23_);
lean_dec(v___x_26_);
v___x_28_ = lean_nat_sub(v___x_27_, v___x_25_);
lean_dec(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0___boxed(lean_object* v_lo_29_, lean_object* v_hi_30_){
_start:
{
uint32_t v_lo_boxed_31_; uint32_t v_hi_boxed_32_; lean_object* v_res_33_; 
v_lo_boxed_31_ = lean_unbox_uint32(v_lo_29_);
lean_dec(v_lo_29_);
v_hi_boxed_32_ = lean_unbox_uint32(v_hi_30_);
lean_dec(v_hi_30_);
v_res_33_ = l_Char_instHasSize__1___lam__0(v_lo_boxed_31_, v_hi_boxed_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0(uint32_t v_hi_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_unsigned_to_nat(1112064u);
v___x_38_ = l_Char_ordinal(v_hi_36_);
v___x_39_ = lean_nat_sub(v___x_37_, v___x_38_);
lean_dec(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0___boxed(lean_object* v_hi_40_){
_start:
{
uint32_t v_hi_boxed_41_; lean_object* v_res_42_; 
v_hi_boxed_41_ = lean_unbox_uint32(v_hi_40_);
lean_dec(v_hi_40_);
v_res_42_ = l_Char_instHasSize__2___lam__0(v_hi_boxed_41_);
return v_res_42_;
}
}
static lean_object* _init_l_Char_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_45_; lean_object* v___x_46_; 
v___x_45_ = 0;
v___x_46_ = lean_box_uint32(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Char_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = l_Char_instLeast_x3f___closed__0___boxed__const__1;
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Char_instLeast_x3f(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Char_instLeast_x3f___closed__0, &l_Char_instLeast_x3f___closed__0_once, _init_l_Char_instLeast_x3f___closed__0);
return v___x_49_;
}
}
lean_object* runtime_initialize_Init_Data_Char_Ordinal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Map(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Char_Ordinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_instLeast_x3f___closed__0___boxed__const__1 = _init_l_Char_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_Char_instLeast_x3f___closed__0___boxed__const__1);
l_Char_instLeast_x3f = _init_l_Char_instLeast_x3f();
lean_mark_persistent(l_Char_instLeast_x3f);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Char(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Char_Ordinal(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Map(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Ordinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Char(builtin);
}
#ifdef __cplusplus
}
#endif
