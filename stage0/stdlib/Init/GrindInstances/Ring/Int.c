// Lean compiler output
// Module: Init.GrindInstances.Ring.Int
// Imports: public import Init.Grind.Ring.Basic public import Init.Data.Int.Lemmas public import Init.Data.Int.Pow import Init.Data.Int.DivMod.Lemmas import Init.Meta
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
lean_object* l_Int_pow___boxed(lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instPowNat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instOfNat(lean_object*);
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_instIntCastInt___lam__0___boxed(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instPowNat___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt___closed__3_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instIntCastInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__8_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt___closed__2_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__9_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOfNat, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__10_value;
static lean_once_cell_t l_Lean_Grind_instCommRingInt___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_instCommRingInt___closed__11;
static lean_once_cell_t l_Lean_Grind_instCommRingInt___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_instCommRingInt___closed__12;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_nat_to_int(v_x1_1_);
v___x_4_ = lean_int_mul(v___x_3_, v_x2_2_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0___boxed(lean_object* v_x1_5_, lean_object* v_x2_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Grind_instCommRingInt___lam__0(v_x1_5_, v_x2_6_);
lean_dec(v_x2_6_);
return v_res_7_;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__11(void){
_start:
{
lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_22_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__5));
v___f_23_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__0));
v___x_24_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__10));
v___f_25_ = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
v___x_26_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__2));
v___x_27_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__1));
v___x_28_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___x_26_);
lean_ctor_set(v___x_28_, 2, v___f_25_);
lean_ctor_set(v___x_28_, 3, v___x_24_);
lean_ctor_set(v___x_28_, 4, v___f_23_);
lean_ctor_set(v___x_28_, 5, v___f_22_);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__12(void){
_start:
{
lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___f_29_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__9));
v___f_30_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__8));
v___x_31_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__7));
v___x_32_ = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__6));
v___x_33_ = lean_obj_once(&l_Lean_Grind_instCommRingInt___closed__11, &l_Lean_Grind_instCommRingInt___closed__11_once, _init_l_Lean_Grind_instCommRingInt___closed__11);
v___x_34_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
lean_ctor_set(v___x_34_, 2, v___x_31_);
lean_ctor_set(v___x_34_, 3, v___f_30_);
lean_ctor_set(v___x_34_, 4, v___f_29_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l_Lean_Grind_instCommRingInt___closed__12, &l_Lean_Grind_instCommRingInt___closed__12_once, _init_l_Lean_Grind_instCommRingInt___closed__12);
return v___x_35_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_Int(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommRingInt = _init_l_Lean_Grind_instCommRingInt();
lean_mark_persistent(l_Lean_Grind_instCommRingInt);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GrindInstances_Ring_Int(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_Ring_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GrindInstances_Ring_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GrindInstances_Ring_Int(builtin);
}
#ifdef __cplusplus
}
#endif
