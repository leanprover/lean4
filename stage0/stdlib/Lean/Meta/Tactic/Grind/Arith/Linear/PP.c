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
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(lean_object* v_as_13_, size_t v_sz_14_, size_t v_i_15_, lean_object* v_b_16_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___boxed(lean_object* v_as_64_, lean_object* v_sz_65_, lean_object* v_i_66_, lean_object* v_b_67_, lean_object* v___y_68_){
_start:
{
size_t v_sz_boxed_69_; size_t v_i_boxed_70_; lean_object* v_res_71_; 
v_sz_boxed_69_ = lean_unbox_usize(v_sz_65_);
lean_dec(v_sz_65_);
v_i_boxed_70_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_64_, v_sz_boxed_69_, v_i_boxed_70_, v_b_67_);
lean_dec_ref(v_as_64_);
return v_res_71_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2(void){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; double v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_75_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4));
v___x_76_ = 1;
v___x_77_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1));
v___x_80_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_75_);
lean_ctor_set_float(v___x_80_, sizeof(void*)*3, v___x_77_);
lean_ctor_set_float(v___x_80_, sizeof(void*)*3 + 8, v___x_77_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*3 + 16, v___x_76_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3));
v___x_83_ = l_Lean_stringToMessageData(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5));
v___x_86_ = l_Lean_stringToMessageData(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(lean_object* v_goal_87_, lean_object* v_s_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_id_94_; lean_object* v_type_95_; lean_object* v___x_96_; 
v_id_94_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_id_94_);
v_type_95_ = lean_ctor_get(v_s_88_, 2);
lean_inc_ref(v_type_95_);
lean_dec_ref(v_s_88_);
v___x_96_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_87_, v_id_94_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_id_94_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_136_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_136_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_array_get_size(v_a_97_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_nat_dec_eq(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; size_t v_sz_105_; size_t v___x_106_; lean_object* v___x_107_; 
lean_del_object(v___x_99_);
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v_sz_105_ = lean_array_size(v_a_97_);
v___x_106_ = ((size_t)0ULL);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_a_97_, v_sz_105_, v___x_106_, v___x_104_);
lean_dec(v_a_97_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_123_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_123_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_123_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_123_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2);
v___x_113_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4);
v___x_114_ = l_Lean_MessageData_ofExpr(v_type_95_);
v___x_115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6);
v___x_117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_112_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
lean_ctor_set(v___x_118_, 2, v_a_108_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_119_);
v___x_121_ = v___x_110_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec_ref(v_type_95_);
v_a_124_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_107_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_107_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_dec(v_a_97_);
lean_dec_ref(v_type_95_);
v___x_132_ = lean_box(0);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_132_);
v___x_134_ = v___x_99_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v_type_95_);
v_a_137_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_96_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_96_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___boxed(lean_object* v_goal_145_, lean_object* v_s_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_145_, v_s_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_goal_145_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(lean_object* v_as_153_, size_t v_sz_154_, size_t v_i_155_, lean_object* v_b_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_153_, v_sz_154_, v_i_155_, v_b_156_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___boxed(lean_object* v_as_163_, lean_object* v_sz_164_, lean_object* v_i_165_, lean_object* v_b_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
size_t v_sz_boxed_172_; size_t v_i_boxed_173_; lean_object* v_res_174_; 
v_sz_boxed_172_ = lean_unbox_usize(v_sz_164_);
lean_dec(v_sz_164_);
v_i_boxed_173_ = lean_unbox_usize(v_i_165_);
lean_dec(v_i_165_);
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(v_as_163_, v_sz_boxed_172_, v_i_boxed_173_, v_b_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec_ref(v_as_163_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(lean_object* v_goal_175_, lean_object* v_as_176_, size_t v_sz_177_, size_t v_i_178_, lean_object* v_b_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = lean_usize_dec_lt(v_i_178_, v_sz_177_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_b_179_);
return v___x_186_;
}
else
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_array_uget_borrowed(v_as_176_, v_i_178_);
lean_inc(v_a_187_);
v___x_188_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_175_, v_a_187_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v_a_191_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v___x_188_);
if (lean_obj_tag(v_a_189_) == 1)
{
lean_object* v_val_195_; lean_object* v___x_196_; 
v_val_195_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_val_195_);
lean_dec_ref(v_a_189_);
v___x_196_ = lean_array_push(v_b_179_, v_val_195_);
v_a_191_ = v___x_196_;
goto v___jp_190_;
}
else
{
lean_dec(v_a_189_);
v_a_191_ = v_b_179_;
goto v___jp_190_;
}
v___jp_190_:
{
size_t v___x_192_; size_t v___x_193_; 
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_add(v_i_178_, v___x_192_);
v_i_178_ = v___x_193_;
v_b_179_ = v_a_191_;
goto _start;
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_b_179_);
v_a_197_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_188_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_188_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0___boxed(lean_object* v_goal_205_, lean_object* v_as_206_, lean_object* v_sz_207_, lean_object* v_i_208_, lean_object* v_b_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
size_t v_sz_boxed_215_; size_t v_i_boxed_216_; lean_object* v_res_217_; 
v_sz_boxed_215_ = lean_unbox_usize(v_sz_207_);
lean_dec(v_sz_207_);
v_i_boxed_216_ = lean_unbox_usize(v_i_208_);
lean_dec(v_i_208_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_205_, v_as_206_, v_sz_boxed_215_, v_i_boxed_216_, v_b_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec_ref(v_as_206_);
lean_dec_ref(v_goal_205_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1));
v___x_222_ = l_Lean_MessageData_ofFormat(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f(lean_object* v_goal_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_230_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_229_, v_goal_223_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_structs_232_; lean_object* v___x_233_; lean_object* v_msgs_234_; size_t v_sz_235_; size_t v___x_236_; lean_object* v___x_237_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v_structs_232_ = lean_ctor_get(v_a_231_, 0);
lean_inc_ref(v_structs_232_);
lean_dec(v_a_231_);
v___x_233_ = lean_unsigned_to_nat(0u);
v_msgs_234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v_sz_235_ = lean_array_size(v_structs_232_);
v___x_236_ = ((size_t)0ULL);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_223_, v_structs_232_, v_sz_235_, v___x_236_, v_msgs_234_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec_ref(v_structs_232_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_262_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_262_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_262_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_262_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_get_size(v_a_238_);
v___x_243_ = lean_nat_dec_eq(v___x_242_, v___x_233_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_dec_eq(v___x_242_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2);
v___x_247_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2);
v___x_248_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
lean_ctor_set(v___x_248_, 2, v_a_238_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_249_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_253_ = lean_array_fget(v_a_238_, v___x_233_);
lean_dec(v_a_238_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_254_);
v___x_256_ = v___x_240_;
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
}
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v_a_238_);
v___x_258_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_258_);
v___x_260_ = v___x_240_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_237_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_237_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_283_; 
v_a_271_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_283_ == 0)
{
v___x_273_ = v___x_230_;
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_230_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v_ref_275_ = lean_ctor_get(v_a_226_, 5);
v___x_276_ = lean_io_error_to_string(v_a_271_);
v___x_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = l_Lean_MessageData_ofFormat(v___x_277_);
lean_inc(v_ref_275_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_ref_275_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_279_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___boxed(lean_object* v_goal_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_goal_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_goal_284_);
return v_res_290_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
