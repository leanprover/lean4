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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__9_value;
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_13_; lean_object* v_intZero_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v_intZero_14_ = lean_nat_to_int(v___x_13_);
return v_intZero_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(lean_object* v_as_16_, size_t v_sz_17_, size_t v_i_18_, lean_object* v_b_19_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lean_usize_dec_lt(v_i_18_, v_sz_17_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_b_19_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_86_; 
v_a_23_ = lean_array_uget(v_as_16_, v_i_18_);
v_fst_24_ = lean_ctor_get(v_a_23_, 0);
v_snd_25_ = lean_ctor_get(v_a_23_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_23_);
if (v_isSharedCheck_86_ == 0)
{
v___x_27_ = v_a_23_;
v_isShared_28_ = v_isSharedCheck_86_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_snd_25_);
lean_inc(v_fst_24_);
lean_dec(v_a_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_86_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; double v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_num_35_; lean_object* v_den_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_85_; 
v___x_29_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v___x_30_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2));
v___x_31_ = lean_box(0);
v___x_32_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
v___x_33_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4));
v___x_34_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_34_, 0, v___x_30_);
lean_ctor_set(v___x_34_, 1, v___x_31_);
lean_ctor_set(v___x_34_, 2, v___x_33_);
lean_ctor_set_float(v___x_34_, sizeof(void*)*3, v___x_32_);
lean_ctor_set_float(v___x_34_, sizeof(void*)*3 + 8, v___x_32_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*3 + 16, v___x_21_);
v_num_35_ = lean_ctor_get(v_snd_25_, 0);
v_den_36_ = lean_ctor_get(v_snd_25_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_snd_25_);
if (v_isSharedCheck_85_ == 0)
{
v___x_38_ = v_snd_25_;
v_isShared_39_ = v_isSharedCheck_85_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_den_36_);
lean_inc(v_num_35_);
lean_dec(v_snd_25_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_85_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_40_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_24_);
v___x_41_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6);
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 7);
lean_ctor_set(v___x_38_, 1, v___x_41_);
lean_ctor_set(v___x_38_, 0, v___x_40_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_84_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
lean_object* v___y_45_; lean_object* v___y_57_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_dec_eq(v_den_36_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v_intZero_64_; uint8_t v_isNeg_65_; 
v_intZero_64_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8);
v_isNeg_65_ = lean_int_dec_lt(v_num_35_, v_intZero_64_);
if (v_isNeg_65_ == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_66_ = lean_nat_abs(v_num_35_);
lean_dec(v_num_35_);
v___x_67_ = l_Nat_reprFast(v_a_66_);
v___y_57_ = v___x_67_;
goto v___jp_56_;
}
else
{
lean_object* v_abs_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_abs_68_ = lean_nat_abs(v_num_35_);
lean_dec(v_num_35_);
v_a_69_ = lean_nat_sub(v_abs_68_, v___x_62_);
lean_dec(v_abs_68_);
v___x_70_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__9));
v___x_71_ = lean_nat_add(v_a_69_, v___x_62_);
lean_dec(v_a_69_);
v___x_72_ = l_Nat_reprFast(v___x_71_);
v___x_73_ = lean_string_append(v___x_70_, v___x_72_);
lean_dec_ref(v___x_72_);
v___y_57_ = v___x_73_;
goto v___jp_56_;
}
}
else
{
lean_object* v_intZero_74_; uint8_t v_isNeg_75_; 
lean_dec(v_den_36_);
v_intZero_74_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__8);
v_isNeg_75_ = lean_int_dec_lt(v_num_35_, v_intZero_74_);
if (v_isNeg_75_ == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; 
v_a_76_ = lean_nat_abs(v_num_35_);
lean_dec(v_num_35_);
v___x_77_ = l_Nat_reprFast(v_a_76_);
v___y_45_ = v___x_77_;
goto v___jp_44_;
}
else
{
lean_object* v_abs_78_; lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_abs_78_ = lean_nat_abs(v_num_35_);
lean_dec(v_num_35_);
v_a_79_ = lean_nat_sub(v_abs_78_, v___x_62_);
lean_dec(v_abs_78_);
v___x_80_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__9));
v___x_81_ = lean_nat_add(v_a_79_, v___x_62_);
lean_dec(v_a_79_);
v___x_82_ = l_Nat_reprFast(v___x_81_);
v___x_83_ = lean_string_append(v___x_80_, v___x_82_);
lean_dec_ref(v___x_82_);
v___y_45_ = v___x_83_;
goto v___jp_44_;
}
}
v___jp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_46_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_46_, 0, v___y_45_);
v___x_47_ = l_Lean_MessageData_ofFormat(v___x_46_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 7);
lean_ctor_set(v___x_27_, 1, v___x_47_);
lean_ctor_set(v___x_27_, 0, v___x_43_);
v___x_49_ = v___x_27_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_55_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; lean_object* v___x_51_; size_t v___x_52_; size_t v___x_53_; 
v___x_50_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_34_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
lean_ctor_set(v___x_50_, 2, v___x_29_);
v___x_51_ = lean_array_push(v_b_19_, v___x_50_);
v___x_52_ = ((size_t)1ULL);
v___x_53_ = lean_usize_add(v_i_18_, v___x_52_);
v_i_18_ = v___x_53_;
v_b_19_ = v___x_51_;
goto _start;
}
}
v___jp_56_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7));
v___x_59_ = lean_string_append(v___y_57_, v___x_58_);
v___x_60_ = l_Nat_reprFast(v_den_36_);
v___x_61_ = lean_string_append(v___x_59_, v___x_60_);
lean_dec_ref(v___x_60_);
v___y_45_ = v___x_61_;
goto v___jp_44_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___boxed(lean_object* v_as_87_, lean_object* v_sz_88_, lean_object* v_i_89_, lean_object* v_b_90_, lean_object* v___y_91_){
_start:
{
size_t v_sz_boxed_92_; size_t v_i_boxed_93_; lean_object* v_res_94_; 
v_sz_boxed_92_ = lean_unbox_usize(v_sz_88_);
lean_dec(v_sz_88_);
v_i_boxed_93_ = lean_unbox_usize(v_i_89_);
lean_dec(v_i_89_);
v_res_94_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_87_, v_sz_boxed_92_, v_i_boxed_93_, v_b_90_);
lean_dec_ref(v_as_87_);
return v_res_94_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2(void){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; double v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4));
v___x_99_ = 1;
v___x_100_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
v___x_101_ = lean_box(0);
v___x_102_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1));
v___x_103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_98_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3, v___x_100_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3 + 8, v___x_100_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 16, v___x_99_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3));
v___x_106_ = l_Lean_stringToMessageData(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5));
v___x_109_ = l_Lean_stringToMessageData(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(lean_object* v_goal_110_, lean_object* v_s_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_id_117_; lean_object* v_type_118_; lean_object* v___x_119_; 
v_id_117_ = lean_ctor_get(v_s_111_, 0);
lean_inc(v_id_117_);
v_type_118_ = lean_ctor_get(v_s_111_, 2);
lean_inc_ref(v_type_118_);
lean_dec_ref(v_s_111_);
v___x_119_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_110_, v_id_117_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_id_117_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_159_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_159_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_159_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_159_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_array_get_size(v_a_120_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; size_t v_sz_128_; size_t v___x_129_; lean_object* v___x_130_; 
lean_del_object(v___x_122_);
v___x_127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v_sz_128_ = lean_array_size(v_a_120_);
v___x_129_ = ((size_t)0ULL);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_a_120_, v_sz_128_, v___x_129_, v___x_127_);
lean_dec(v_a_120_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_146_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_146_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_146_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_146_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2);
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4);
v___x_137_ = l_Lean_MessageData_ofExpr(v_type_118_);
v___x_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_141_, 0, v___x_135_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
lean_ctor_set(v___x_141_, 2, v_a_131_);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_142_);
v___x_144_ = v___x_133_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_type_118_);
v_a_147_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_130_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_130_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec(v_a_120_);
lean_dec_ref(v_type_118_);
v___x_155_ = lean_box(0);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_155_);
v___x_157_ = v___x_122_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_type_118_);
v_a_160_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_119_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_119_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___boxed(lean_object* v_goal_168_, lean_object* v_s_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_168_, v_s_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(lean_object* v_as_176_, size_t v_sz_177_, size_t v_i_178_, lean_object* v_b_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_176_, v_sz_177_, v_i_178_, v_b_179_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___boxed(lean_object* v_as_186_, lean_object* v_sz_187_, lean_object* v_i_188_, lean_object* v_b_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
size_t v_sz_boxed_195_; size_t v_i_boxed_196_; lean_object* v_res_197_; 
v_sz_boxed_195_ = lean_unbox_usize(v_sz_187_);
lean_dec(v_sz_187_);
v_i_boxed_196_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_res_197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(v_as_186_, v_sz_boxed_195_, v_i_boxed_196_, v_b_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec_ref(v_as_186_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(lean_object* v_goal_198_, lean_object* v_as_199_, size_t v_sz_200_, size_t v_i_201_, lean_object* v_b_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = lean_usize_dec_lt(v_i_201_, v_sz_200_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec_ref(v_goal_198_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_b_202_);
return v___x_209_;
}
else
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_array_uget_borrowed(v_as_199_, v_i_201_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc(v_a_210_);
lean_inc_ref(v_goal_198_);
v___x_211_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(v_goal_198_, v_a_210_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_a_214_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_218_);
lean_dec_ref(v_a_212_);
v___x_219_ = lean_array_push(v_b_202_, v_val_218_);
v_a_214_ = v___x_219_;
goto v___jp_213_;
}
else
{
lean_dec(v_a_212_);
v_a_214_ = v_b_202_;
goto v___jp_213_;
}
v___jp_213_:
{
size_t v___x_215_; size_t v___x_216_; 
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_add(v_i_201_, v___x_215_);
v_i_201_ = v___x_216_;
v_b_202_ = v_a_214_;
goto _start;
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec_ref(v_b_202_);
lean_dec_ref(v_goal_198_);
v_a_220_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_211_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_211_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0___boxed(lean_object* v_goal_228_, lean_object* v_as_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_b_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
size_t v_sz_boxed_238_; size_t v_i_boxed_239_; lean_object* v_res_240_; 
v_sz_boxed_238_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_239_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_228_, v_as_229_, v_sz_boxed_238_, v_i_boxed_239_, v_b_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec_ref(v_as_229_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1));
v___x_245_ = l_Lean_MessageData_ofFormat(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f(lean_object* v_goal_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_253_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_252_, v_goal_246_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v_structs_255_; lean_object* v___x_256_; lean_object* v_msgs_257_; size_t v_sz_258_; size_t v___x_259_; lean_object* v___x_260_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref(v___x_253_);
v_structs_255_ = lean_ctor_get(v_a_254_, 0);
lean_inc_ref(v_structs_255_);
lean_dec(v_a_254_);
v___x_256_ = lean_unsigned_to_nat(0u);
v_msgs_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0));
v_sz_258_ = lean_array_size(v_structs_255_);
v___x_259_ = ((size_t)0ULL);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_246_, v_structs_255_, v_sz_258_, v___x_259_, v_msgs_257_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec_ref(v_structs_255_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_285_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_285_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_285_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_285_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_array_get_size(v_a_261_);
v___x_266_ = lean_nat_dec_eq(v___x_265_, v___x_256_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_dec_eq(v___x_265_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_269_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2);
v___x_270_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2);
v___x_271_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
lean_ctor_set(v___x_271_, 2, v_a_261_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_272_);
v___x_274_ = v___x_263_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_array_fget(v_a_261_, v___x_256_);
lean_dec(v_a_261_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_277_);
v___x_279_ = v___x_263_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec(v_a_261_);
v___x_281_ = lean_box(0);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_281_);
v___x_283_ = v___x_263_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_260_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_260_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_a_250_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_goal_246_);
v_a_294_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_306_ == 0)
{
v___x_296_ = v___x_253_;
v_isShared_297_ = v_isSharedCheck_306_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_253_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_306_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_ref_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v_ref_298_ = lean_ctor_get(v_a_249_, 5);
lean_inc(v_ref_298_);
lean_dec_ref(v_a_249_);
v___x_299_ = lean_io_error_to_string(v_a_294_);
v___x_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = l_Lean_MessageData_ofFormat(v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_ref_298_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_302_);
v___x_304_ = v___x_296_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f___boxed(lean_object* v_goal_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_goal_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v_res_313_;
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
