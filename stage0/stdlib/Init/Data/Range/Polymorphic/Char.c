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
lean_object* l_Char_instHasSize___lam__0(uint32_t v_lo_7_, uint32_t v_hi_8_){
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
LEAN_EXPORT void l_Char_instHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_7_ = stack[0].m_num;
uint32_t v_hi_8_ = stack[1].m_num;
lean_object* v_res_14_;
v_res_14_ = l_Char_instHasSize___lam__0(v_lo_7_, v_hi_8_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0___boxed(lean_object* v_lo_15_, lean_object* v_hi_16_){
_start:
{
uint32_t v_lo_boxed_17_; uint32_t v_hi_boxed_18_; lean_object* v_res_19_; 
v_lo_boxed_17_ = lean_unbox_uint32(v_lo_15_);
lean_dec(v_lo_15_);
v_hi_boxed_18_ = lean_unbox_uint32(v_hi_16_);
lean_dec(v_hi_16_);
v_res_19_ = l_Char_instHasSize___lam__0(v_lo_boxed_17_, v_hi_boxed_18_);
return v_res_19_;
}
}
lean_object* l_Char_instHasSize__1___lam__0(uint32_t v_lo_22_, uint32_t v_hi_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_24_ = l_Char_ordinal(v_lo_22_);
v___x_25_ = l_Char_ordinal(v_hi_23_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v___x_25_, v___x_26_);
lean_dec(v___x_25_);
v___x_28_ = lean_nat_sub(v___x_27_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_sub(v___x_28_, v___x_26_);
lean_dec(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Char_instHasSize__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_22_ = stack[0].m_num;
uint32_t v_hi_23_ = stack[1].m_num;
lean_object* v_res_30_;
v_res_30_ = l_Char_instHasSize__1___lam__0(v_lo_22_, v_hi_23_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0___boxed(lean_object* v_lo_31_, lean_object* v_hi_32_){
_start:
{
uint32_t v_lo_boxed_33_; uint32_t v_hi_boxed_34_; lean_object* v_res_35_; 
v_lo_boxed_33_ = lean_unbox_uint32(v_lo_31_);
lean_dec(v_lo_31_);
v_hi_boxed_34_ = lean_unbox_uint32(v_hi_32_);
lean_dec(v_hi_32_);
v_res_35_ = l_Char_instHasSize__1___lam__0(v_lo_boxed_33_, v_hi_boxed_34_);
return v_res_35_;
}
}
lean_object* l_Char_instHasSize__2___lam__0(uint32_t v_hi_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_unsigned_to_nat(1112064u);
v___x_40_ = l_Char_ordinal(v_hi_38_);
v___x_41_ = lean_nat_sub(v___x_39_, v___x_40_);
lean_dec(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Char_instHasSize__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_hi_38_ = stack[0].m_num;
lean_object* v_res_42_;
v_res_42_ = l_Char_instHasSize__2___lam__0(v_hi_38_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0___boxed(lean_object* v_hi_43_){
_start:
{
uint32_t v_hi_boxed_44_; lean_object* v_res_45_; 
v_hi_boxed_44_ = lean_unbox_uint32(v_hi_43_);
lean_dec(v_hi_43_);
v_res_45_ = l_Char_instHasSize__2___lam__0(v_hi_boxed_44_);
return v_res_45_;
}
}
static lean_object* _init_l_Char_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_48_; lean_object* v___x_49_; 
v___x_48_ = 0;
v___x_49_ = lean_box_uint32(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Char_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Char_instLeast_x3f___closed__0___boxed__const__1;
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Char_instLeast_x3f(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Char_instLeast_x3f___closed__0, &l_Char_instLeast_x3f___closed__0_once, _init_l_Char_instLeast_x3f___closed__0);
return v___x_52_;
}
}
lean_object* runtime_initialize_Init_Data_Char_Ordinal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Map(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
