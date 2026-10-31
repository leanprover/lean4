// Lean compiler output
// Module: Init.Data.Array.MinMax
// Imports: public import Init.Data.Array.Lemmas import Init.Data.List.MinMax public import Init.Data.Order.Classes import Init.Data.Array.Bootstrap import Init.Data.Array.DecidableEq import Init.Data.List.TakeDrop import Init.Data.Order.Lemmas
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__0 = (const lean_object*)&l_Array_min___redArg___closed__0_value;
static const lean_closure_object l_Array_min___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__1 = (const lean_object*)&l_Array_min___redArg___closed__1_value;
static const lean_closure_object l_Array_min___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__2 = (const lean_object*)&l_Array_min___redArg___closed__2_value;
static const lean_closure_object l_Array_min___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__3 = (const lean_object*)&l_Array_min___redArg___closed__3_value;
static const lean_closure_object l_Array_min___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__4 = (const lean_object*)&l_Array_min___redArg___closed__4_value;
static const lean_closure_object l_Array_min___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__5 = (const lean_object*)&l_Array_min___redArg___closed__5_value;
static const lean_closure_object l_Array_min___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__6 = (const lean_object*)&l_Array_min___redArg___closed__6_value;
static const lean_ctor_object l_Array_min___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_min___redArg___closed__0_value),((lean_object*)&l_Array_min___redArg___closed__1_value)}};
static const lean_object* l_Array_min___redArg___closed__7 = (const lean_object*)&l_Array_min___redArg___closed__7_value;
static const lean_ctor_object l_Array_min___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_min___redArg___closed__7_value),((lean_object*)&l_Array_min___redArg___closed__2_value),((lean_object*)&l_Array_min___redArg___closed__3_value),((lean_object*)&l_Array_min___redArg___closed__4_value),((lean_object*)&l_Array_min___redArg___closed__5_value)}};
static const lean_object* l_Array_min___redArg___closed__8 = (const lean_object*)&l_Array_min___redArg___closed__8_value;
static const lean_ctor_object l_Array_min___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_min___redArg___closed__8_value),((lean_object*)&l_Array_min___redArg___closed__6_value)}};
static const lean_object* l_Array_min___redArg___closed__9 = (const lean_object*)&l_Array_min___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_min___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_x1_2_, lean_object* v_x2_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_x1_2_, v_x2_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Array_min___redArg(lean_object* v_inst_24_, lean_object* v_arr_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_array_fget(v_arr_25_, v___x_26_);
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_array_get_size(v_arr_25_);
v___x_30_ = ((lean_object*)(l_Array_min___redArg___closed__9));
v___x_31_ = lean_nat_dec_lt(v___x_28_, v___x_29_);
if (v___x_31_ == 0)
{
lean_dec_ref(v_arr_25_);
lean_dec(v_inst_24_);
return v___x_27_;
}
else
{
lean_object* v___f_32_; size_t v___x_33_; size_t v___x_34_; lean_object* v___x_35_; 
v___f_32_ = lean_alloc_closure((void*)(l_Array_min___redArg___lam__0), 3, 1);
lean_closure_set(v___f_32_, 0, v_inst_24_);
v___x_33_ = ((size_t)1ULL);
v___x_34_ = lean_usize_of_nat(v___x_29_);
v___x_35_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_30_, v___f_32_, v_arr_25_, v___x_33_, v___x_34_, v___x_27_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_arr_38_, lean_object* v_h_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Array_min___redArg(v_inst_37_, v_arr_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___redArg(lean_object* v_inst_41_, lean_object* v_arr_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = lean_array_get_size(v_arr_42_);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = l_Array_min___redArg(v_inst_41_, v_arr_42_);
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
else
{
lean_object* v___x_48_; 
lean_dec_ref(v_arr_42_);
lean_dec(v_inst_41_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_arr_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Array_min_x3f___redArg(v_inst_50_, v_arr_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Array_max___redArg(lean_object* v_inst_53_, lean_object* v_arr_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_array_fget(v_arr_54_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_array_get_size(v_arr_54_);
v___x_59_ = ((lean_object*)(l_Array_min___redArg___closed__9));
v___x_60_ = lean_nat_dec_lt(v___x_57_, v___x_58_);
if (v___x_60_ == 0)
{
lean_dec_ref(v_arr_54_);
lean_dec(v_inst_53_);
return v___x_56_;
}
else
{
lean_object* v___f_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; 
v___f_61_ = lean_alloc_closure((void*)(l_Array_min___redArg___lam__0), 3, 1);
lean_closure_set(v___f_61_, 0, v_inst_53_);
v___x_62_ = ((size_t)1ULL);
v___x_63_ = lean_usize_of_nat(v___x_58_);
v___x_64_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_59_, v___f_61_, v_arr_54_, v___x_62_, v___x_63_, v___x_56_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_arr_67_, lean_object* v_h_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Array_max___redArg(v_inst_66_, v_arr_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___redArg(lean_object* v_inst_70_, lean_object* v_arr_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = lean_array_get_size(v_arr_71_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_nat_dec_eq(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = l_Array_max___redArg(v_inst_70_, v_arr_71_);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; 
lean_dec_ref(v_arr_71_);
lean_dec(v_inst_70_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_, lean_object* v_arr_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Array_max_x3f___redArg(v_inst_79_, v_arr_80_);
return v___x_81_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_MinMax(builtin);
}
#ifdef __cplusplus
}
#endif
