// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.PP
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.Types import Lean.Meta.Tactic.Grind.Arith.Linear.Model import Lean.Meta.Tactic.Grind.Arith.Util import Init.Omega
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assign"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(140, 147, 101, 187, 172, 93, 80, 64)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 239, 24, 66, 70, 17, 119, 33)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Linarith assignment for `"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; double v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_float_of_nat(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5));
v___x_11_ = l_Lean_stringToMessageData(v___x_10_);
return v___x_11_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(lean_object* v_as_13_, size_t v_sz_14_, size_t v_i_15_, lean_object* v_b_16_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_lt(v_i_15_, v_sz_14_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v_b_16_);
return v___x_19_;
}
else
{
lean_object* v_a_20_; lean_object* v_fst_21_; lean_object* v_snd_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_63_; 
v_a_20_ = lean_array_uget(v_as_13_, v_i_15_);
v_fst_21_ = lean_ctor_get(v_a_20_, 0);
v_snd_22_ = lean_ctor_get(v_a_20_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_a_20_);
if (v_isSharedCheck_63_ == 0)
{
v___x_24_ = v_a_20_;
v_isShared_25_ = v_isSharedCheck_63_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_snd_22_);
lean_inc(v_fst_21_);
lean_dec(v_a_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_63_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; double v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_num_32_; lean_object* v_den_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_62_; 
v___x_26_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v___x_27_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2));
v___x_28_ = lean_box(0);
v___x_29_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
v___x_30_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4));
v___x_31_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_31_, 0, v___x_27_);
lean_ctor_set(v___x_31_, 1, v___x_28_);
lean_ctor_set(v___x_31_, 2, v___x_30_);
lean_ctor_set_float(v___x_31_, sizeof(void*)*3, v___x_29_);
lean_ctor_set_float(v___x_31_, sizeof(void*)*3 + 8, v___x_29_);
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*3 + 16, v___x_18_);
v_num_32_ = lean_ctor_get(v_snd_22_, 0);
v_den_33_ = lean_ctor_get(v_snd_22_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_snd_22_);
if (v_isSharedCheck_62_ == 0)
{
v___x_35_ = v_snd_22_;
v_isShared_36_ = v_isSharedCheck_62_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_den_33_);
lean_inc(v_num_32_);
lean_dec(v_snd_22_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_62_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_37_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_21_);
v___x_38_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 7);
lean_ctor_set(v___x_35_, 1, v___x_38_);
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_40_ = v___x_35_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_61_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___y_42_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_dec_eq(v_den_33_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_55_ = l_Int_repr(v_num_32_);
lean_dec(v_num_32_);
v___x_56_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7));
v___x_57_ = lean_string_append(v___x_55_, v___x_56_);
v___x_58_ = l_Nat_reprFast(v_den_33_);
v___x_59_ = lean_string_append(v___x_57_, v___x_58_);
lean_dec_ref(v___x_58_);
v___y_42_ = v___x_59_;
goto v___jp_41_;
}
else
{
lean_object* v___x_60_; 
lean_dec(v_den_33_);
v___x_60_ = l_Int_repr(v_num_32_);
lean_dec(v_num_32_);
v___y_42_ = v___x_60_;
goto v___jp_41_;
}
v___jp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_43_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_43_, 0, v___y_42_);
v___x_44_ = l_Lean_MessageData_ofFormat(v___x_43_);
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 7);
lean_ctor_set(v___x_24_, 1, v___x_44_);
lean_ctor_set(v___x_24_, 0, v___x_40_);
v___x_46_ = v___x_24_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_44_);
v___x_46_ = v_reuseFailAlloc_52_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; size_t v___x_49_; size_t v___x_50_; 
v___x_47_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_47_, 0, v___x_31_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
lean_ctor_set(v___x_47_, 2, v___x_26_);
v___x_48_ = lean_array_push(v_b_16_, v___x_47_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_15_, v___x_49_);
v_i_15_ = v___x_50_;
v_b_16_ = v___x_48_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_13_ = stack[0].m_obj;
size_t v_sz_14_ = stack[1].m_num;
size_t v_i_15_ = stack[2].m_num;
lean_object* v_b_16_ = stack[3].m_obj;
lean_object* v_res_64_;
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_13_, v_sz_14_, v_i_15_, v_b_16_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___boxed(lean_object* v_as_65_, lean_object* v_sz_66_, lean_object* v_i_67_, lean_object* v_b_68_, lean_object* v___y_69_){
_start:
{
size_t v_sz_boxed_70_; size_t v_i_boxed_71_; lean_object* v_res_72_; 
v_sz_boxed_70_ = lean_unbox_usize(v_sz_66_);
lean_dec(v_sz_66_);
v_i_boxed_71_ = lean_unbox_usize(v_i_67_);
lean_dec(v_i_67_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_65_, v_sz_boxed_70_, v_i_boxed_71_, v_b_68_);
lean_dec_ref(v_as_65_);
return v_res_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2(void){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; double v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_76_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4));
v___x_77_ = 1;
v___x_78_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
v___x_79_ = lean_box(0);
v___x_80_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1));
v___x_81_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_76_);
lean_ctor_set_float(v___x_81_, sizeof(void*)*3, v___x_78_);
lean_ctor_set_float(v___x_81_, sizeof(void*)*3 + 8, v___x_78_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*3 + 16, v___x_77_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3));
v___x_84_ = l_Lean_stringToMessageData(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5));
v___x_87_ = l_Lean_stringToMessageData(v___x_86_);
return v___x_87_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(lean_object* v_goal_88_, lean_object* v_s_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_id_95_; lean_object* v_type_96_; lean_object* v___x_97_; 
v_id_95_ = lean_ctor_get(v_s_89_, 0);
lean_inc(v_id_95_);
v_type_96_ = lean_ctor_get(v_s_89_, 2);
lean_inc_ref(v_type_96_);
lean_dec_ref(v_s_89_);
v___x_97_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_88_, v_id_95_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_id_95_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_137_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_137_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_137_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_137_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = lean_array_get_size(v_a_98_);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_dec_eq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; size_t v_sz_106_; size_t v___x_107_; lean_object* v___x_108_; 
lean_del_object(v___x_100_);
v___x_105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v_sz_106_ = lean_array_size(v_a_98_);
v___x_107_ = ((size_t)0ULL);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_a_98_, v_sz_106_, v___x_107_, v___x_105_);
lean_dec(v_a_98_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_124_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_124_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_124_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_124_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_113_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2);
v___x_114_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4);
v___x_115_ = l_Lean_MessageData_ofExpr(v_type_96_);
v___x_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6);
v___x_118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_119_, 0, v___x_113_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_ctor_set(v___x_119_, 2, v_a_109_);
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_120_);
v___x_122_ = v___x_111_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_type_96_);
v_a_125_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_108_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_108_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_dec(v_a_98_);
lean_dec_ref(v_type_96_);
v___x_133_ = lean_box(0);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_133_);
v___x_135_ = v___x_100_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec_ref(v_type_96_);
v_a_138_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_97_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_97_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_88_ = stack[0].m_obj;
lean_object* v_s_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v_a_91_ = stack[3].m_obj;
lean_object* v_a_92_ = stack[4].m_obj;
lean_object* v_a_93_ = stack[5].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_88_, v_s_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___boxed(lean_object* v_goal_147_, lean_object* v_s_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_147_, v_s_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec_ref(v_goal_147_);
return v_res_154_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(lean_object* v_as_155_, size_t v_sz_156_, size_t v_i_157_, lean_object* v_b_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_155_, v_sz_156_, v_i_157_, v_b_158_);
return v___x_164_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_155_ = stack[0].m_obj;
size_t v_sz_156_ = stack[1].m_num;
size_t v_i_157_ = stack[2].m_num;
lean_object* v_b_158_ = stack[3].m_obj;
lean_object* v___y_159_ = stack[4].m_obj;
lean_object* v___y_160_ = stack[5].m_obj;
lean_object* v___y_161_ = stack[6].m_obj;
lean_object* v___y_162_ = stack[7].m_obj;
lean_object* v_res_165_;
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(v_as_155_, v_sz_156_, v_i_157_, v_b_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___boxed(lean_object* v_as_166_, lean_object* v_sz_167_, lean_object* v_i_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
size_t v_sz_boxed_175_; size_t v_i_boxed_176_; lean_object* v_res_177_; 
v_sz_boxed_175_ = lean_unbox_usize(v_sz_167_);
lean_dec(v_sz_167_);
v_i_boxed_176_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(v_as_166_, v_sz_boxed_175_, v_i_boxed_176_, v_b_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec_ref(v_as_166_);
return v_res_177_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(lean_object* v_goal_178_, lean_object* v_as_179_, size_t v_sz_180_, size_t v_i_181_, lean_object* v_b_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_a_189_; uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_lt(v_i_181_, v_sz_180_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v_b_182_);
return v___x_194_;
}
else
{
lean_object* v_a_195_; lean_object* v___x_196_; 
v_a_195_ = lean_array_uget_borrowed(v_as_179_, v_i_181_);
lean_inc(v_a_195_);
v___x_196_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_178_, v_a_195_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
if (lean_obj_tag(v_a_197_) == 1)
{
lean_object* v_val_198_; lean_object* v___x_199_; 
v_val_198_ = lean_ctor_get(v_a_197_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v_a_197_, 1);
v___x_199_ = lean_array_push(v_b_182_, v_val_198_);
v_a_189_ = v___x_199_;
goto v___jp_188_;
}
else
{
lean_dec(v_a_197_);
v_a_189_ = v_b_182_;
goto v___jp_188_;
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_b_182_);
v_a_200_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_196_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
v___jp_188_:
{
size_t v___x_190_; size_t v___x_191_; 
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_181_, v___x_190_);
v_i_181_ = v___x_191_;
v_b_182_ = v_a_189_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_178_ = stack[0].m_obj;
lean_object* v_as_179_ = stack[1].m_obj;
size_t v_sz_180_ = stack[2].m_num;
size_t v_i_181_ = stack[3].m_num;
lean_object* v_b_182_ = stack[4].m_obj;
lean_object* v___y_183_ = stack[5].m_obj;
lean_object* v___y_184_ = stack[6].m_obj;
lean_object* v___y_185_ = stack[7].m_obj;
lean_object* v___y_186_ = stack[8].m_obj;
lean_object* v_res_208_;
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_178_, v_as_179_, v_sz_180_, v_i_181_, v_b_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0___boxed(lean_object* v_goal_209_, lean_object* v_as_210_, lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_220_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_209_, v_as_210_, v_sz_boxed_219_, v_i_boxed_220_, v_b_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
lean_dec_ref(v_goal_209_);
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1));
v___x_226_ = l_Lean_MessageData_ofFormat(v___x_225_);
return v___x_226_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f(lean_object* v_goal_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v_msgs_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_ref_233_ = lean_ctor_get(v_a_230_, 2);
v___x_234_ = lean_unsigned_to_nat(0u);
v_msgs_235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v___x_236_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_237_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_236_, v_goal_227_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v_structs_239_; size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v_structs_239_ = lean_ctor_get(v_a_238_, 0);
lean_inc_ref(v_structs_239_);
lean_dec(v_a_238_);
v_sz_240_ = lean_array_size(v_structs_239_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_227_, v_structs_239_, v_sz_240_, v___x_241_, v_msgs_235_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec_ref(v_structs_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_267_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_267_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_267_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_267_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_array_get_size(v_a_243_);
v___x_248_ = lean_nat_dec_eq(v___x_247_, v___x_234_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_dec_eq(v___x_247_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_251_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2);
v___x_252_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2);
v___x_253_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
lean_ctor_set(v___x_253_, 2, v_a_243_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_254_);
v___x_256_ = v___x_245_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_258_ = lean_array_fget(v_a_243_, v___x_234_);
lean_dec(v_a_243_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_259_);
v___x_261_ = v___x_245_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_dec(v_a_243_);
v___x_263_ = lean_box(0);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_263_);
v___x_265_ = v___x_245_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
v_a_268_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_242_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_242_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_287_; 
v_a_276_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_287_ == 0)
{
v___x_278_ = v___x_237_;
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_237_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_280_ = lean_io_error_to_string(v_a_276_);
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
lean_inc(v_ref_233_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_ref_233_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_283_);
v___x_285_ = v___x_278_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_pp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_227_ = stack[0].m_obj;
lean_object* v_a_228_ = stack[1].m_obj;
lean_object* v_a_229_ = stack[2].m_obj;
lean_object* v_a_230_ = stack[3].m_obj;
lean_object* v_a_231_ = stack[4].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_goal_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___boxed(lean_object* v_goal_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_goal_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec_ref(v_goal_289_);
return v_res_295_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
}
#ifdef __cplusplus
}
#endif
