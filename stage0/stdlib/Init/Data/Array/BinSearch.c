// Lean compiler output
// Module: Init.Data.Array.BinSearch
// Imports: public import Init.Data.Array.Basic import Init.Data.Bool import Init.Omega import Init.WFTactics
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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Option_isSome___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_binSearch___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_binSearch___redArg___closed__0 = (const lean_object*)&l_Array_binSearch___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_binSearch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_binSearchContains___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_isSome___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_binSearchContains___redArg___closed__0 = (const lean_object*)&l_Array_binSearchContains___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Array_binSearchContains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchContains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchContains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchContains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Array_binInsert___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__0 = (const lean_object*)&l_Array_binInsert___redArg___closed__0_value;
static const lean_closure_object l_Array_binInsert___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__1 = (const lean_object*)&l_Array_binInsert___redArg___closed__1_value;
static const lean_closure_object l_Array_binInsert___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__2 = (const lean_object*)&l_Array_binInsert___redArg___closed__2_value;
static const lean_closure_object l_Array_binInsert___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__3 = (const lean_object*)&l_Array_binInsert___redArg___closed__3_value;
static const lean_closure_object l_Array_binInsert___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__4 = (const lean_object*)&l_Array_binInsert___redArg___closed__4_value;
static const lean_closure_object l_Array_binInsert___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__5 = (const lean_object*)&l_Array_binInsert___redArg___closed__5_value;
static const lean_closure_object l_Array_binInsert___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_binInsert___redArg___closed__6 = (const lean_object*)&l_Array_binInsert___redArg___closed__6_value;
static const lean_ctor_object l_Array_binInsert___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_binInsert___redArg___closed__0_value),((lean_object*)&l_Array_binInsert___redArg___closed__1_value)}};
static const lean_object* l_Array_binInsert___redArg___closed__7 = (const lean_object*)&l_Array_binInsert___redArg___closed__7_value;
static const lean_ctor_object l_Array_binInsert___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_binInsert___redArg___closed__7_value),((lean_object*)&l_Array_binInsert___redArg___closed__2_value),((lean_object*)&l_Array_binInsert___redArg___closed__3_value),((lean_object*)&l_Array_binInsert___redArg___closed__4_value),((lean_object*)&l_Array_binInsert___redArg___closed__5_value)}};
static const lean_object* l_Array_binInsert___redArg___closed__8 = (const lean_object*)&l_Array_binInsert___redArg___closed__8_value;
static const lean_ctor_object l_Array_binInsert___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_binInsert___redArg___closed__8_value),((lean_object*)&l_Array_binInsert___redArg___closed__6_value)}};
static const lean_object* l_Array_binInsert___redArg___closed__9 = (const lean_object*)&l_Array_binInsert___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_binInsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___redArg(lean_object* v_lt_1_, lean_object* v_found_2_, lean_object* v_as_3_, lean_object* v_k_4_, lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_m_12_; lean_object* v_a_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_10_ = lean_nat_add(v_x_5_, v_x_6_);
v___x_11_ = lean_unsigned_to_nat(1u);
v_m_12_ = lean_nat_shiftr(v___x_10_, v___x_11_);
lean_dec(v___x_10_);
v_a_13_ = lean_array_fget_borrowed(v_as_3_, v_m_12_);
lean_inc_ref(v_lt_1_);
lean_inc(v_k_4_);
lean_inc(v_a_13_);
v___x_14_ = lean_apply_2(v_lt_1_, v_a_13_, v_k_4_);
v___x_15_ = lean_unbox(v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; uint8_t v___x_17_; 
lean_dec(v_x_6_);
lean_inc_ref(v_lt_1_);
lean_inc(v_a_13_);
lean_inc(v_k_4_);
v___x_16_ = lean_apply_2(v_lt_1_, v_k_4_, v_a_13_);
v___x_17_ = lean_unbox(v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_m_12_);
lean_dec(v_x_5_);
lean_dec(v_k_4_);
lean_dec_ref(v_lt_1_);
lean_inc(v_a_13_);
v___x_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_18_, 0, v_a_13_);
v___x_19_ = lean_apply_1(v_found_2_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_nat_dec_eq(v_m_12_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_nat_sub(v_m_12_, v___x_11_);
lean_dec(v_m_12_);
v___x_23_ = lean_nat_dec_lt(v___x_22_, v_x_5_);
if (v___x_23_ == 0)
{
v_x_6_ = v___x_22_;
goto _start;
}
else
{
lean_dec(v___x_22_);
lean_dec(v_x_5_);
lean_dec(v_k_4_);
lean_dec_ref(v_lt_1_);
goto v___jp_7_;
}
}
else
{
lean_dec(v_m_12_);
lean_dec(v_x_5_);
lean_dec(v_k_4_);
lean_dec_ref(v_lt_1_);
goto v___jp_7_;
}
}
}
else
{
lean_object* v___x_25_; uint8_t v___x_26_; 
lean_dec(v_x_5_);
v___x_25_ = lean_nat_add(v_m_12_, v___x_11_);
lean_dec(v_m_12_);
v___x_26_ = lean_nat_dec_le(v___x_25_, v_x_6_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v___x_25_);
lean_dec(v_x_6_);
lean_dec(v_k_4_);
lean_dec_ref(v_lt_1_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_apply_1(v_found_2_, v___x_27_);
return v___x_28_;
}
else
{
v_x_5_ = v___x_25_;
goto _start;
}
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_apply_1(v_found_2_, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___redArg___boxed(lean_object* v_lt_30_, lean_object* v_found_31_, lean_object* v_as_32_, lean_object* v_k_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Array_binSearchAux___redArg(v_lt_30_, v_found_31_, v_as_32_, v_k_33_, v_x_34_, v_x_35_);
lean_dec_ref(v_as_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux(lean_object* v_00_u03b1_37_, lean_object* v_00_u03b2_38_, lean_object* v_lt_39_, lean_object* v_found_40_, lean_object* v_as_41_, lean_object* v_k_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Array_binSearchAux___redArg(v_lt_39_, v_found_40_, v_as_41_, v_k_42_, v_x_43_, v_x_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___boxed(lean_object* v_00_u03b1_47_, lean_object* v_00_u03b2_48_, lean_object* v_lt_49_, lean_object* v_found_50_, lean_object* v_as_51_, lean_object* v_k_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Array_binSearchAux(v_00_u03b1_47_, v_00_u03b2_48_, v_lt_49_, v_found_50_, v_as_51_, v_k_52_, v_x_53_, v_x_54_, v_x_55_);
lean_dec_ref(v_as_51_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter___redArg(lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_h__1_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_apply_3(v_h__1_59_, v_x_57_, v_x_58_, lean_box(0));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter(lean_object* v_00_u03b1_61_, lean_object* v_as_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_h__1_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_apply_3(v_h__1_67_, v_x_64_, v_x_65_, lean_box(0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter___boxed(lean_object* v_00_u03b1_69_, lean_object* v_as_70_, lean_object* v_motive_71_, lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_h__1_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter(v_00_u03b1_69_, v_as_70_, v_motive_71_, v_x_72_, v_x_73_, v_x_74_, v_h__1_75_);
lean_dec_ref(v_as_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearch___redArg(lean_object* v_as_78_, lean_object* v_k_79_, lean_object* v_lt_80_, lean_object* v_lo_81_, lean_object* v_hi_82_){
_start:
{
lean_object* v___y_84_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_array_get_size(v_as_78_);
v___x_90_ = lean_nat_dec_lt(v_lo_81_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v_hi_82_);
lean_dec(v_lo_81_);
lean_dec_ref(v_lt_80_);
lean_dec(v_k_79_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_lt(v_hi_82_, v___x_89_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_hi_82_);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_sub(v___x_89_, v___x_93_);
v___y_84_ = v___x_94_;
goto v___jp_83_;
}
else
{
v___y_84_ = v_hi_82_;
goto v___jp_83_;
}
}
v___jp_83_:
{
uint8_t v___x_85_; 
v___x_85_ = lean_nat_dec_le(v_lo_81_, v___y_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v___y_84_);
lean_dec(v_lo_81_);
lean_dec_ref(v_lt_80_);
lean_dec(v_k_79_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Array_binSearch___redArg___closed__0));
v___x_88_ = l_Array_binSearchAux___redArg(v_lt_80_, v___x_87_, v_as_78_, v_k_79_, v_lo_81_, v___y_84_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearch___redArg___boxed(lean_object* v_as_95_, lean_object* v_k_96_, lean_object* v_lt_97_, lean_object* v_lo_98_, lean_object* v_hi_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Array_binSearch___redArg(v_as_95_, v_k_96_, v_lt_97_, v_lo_98_, v_hi_99_);
lean_dec_ref(v_as_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearch(lean_object* v_00_u03b1_101_, lean_object* v_as_102_, lean_object* v_k_103_, lean_object* v_lt_104_, lean_object* v_lo_105_, lean_object* v_hi_106_){
_start:
{
lean_object* v___y_108_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_array_get_size(v_as_102_);
v___x_114_ = lean_nat_dec_lt(v_lo_105_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec(v_hi_106_);
lean_dec(v_lo_105_);
lean_dec_ref(v_lt_104_);
lean_dec(v_k_103_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = lean_nat_dec_lt(v_hi_106_, v___x_113_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_hi_106_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_sub(v___x_113_, v___x_117_);
v___y_108_ = v___x_118_;
goto v___jp_107_;
}
else
{
v___y_108_ = v_hi_106_;
goto v___jp_107_;
}
}
v___jp_107_:
{
uint8_t v___x_109_; 
v___x_109_ = lean_nat_dec_le(v_lo_105_, v___y_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_dec(v___y_108_);
lean_dec(v_lo_105_);
lean_dec_ref(v_lt_104_);
lean_dec(v_k_103_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Array_binSearch___redArg___closed__0));
v___x_112_ = l_Array_binSearchAux___redArg(v_lt_104_, v___x_111_, v_as_102_, v_k_103_, v_lo_105_, v___y_108_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearch___boxed(lean_object* v_00_u03b1_119_, lean_object* v_as_120_, lean_object* v_k_121_, lean_object* v_lt_122_, lean_object* v_lo_123_, lean_object* v_hi_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Array_binSearch(v_00_u03b1_119_, v_as_120_, v_k_121_, v_lt_122_, v_lo_123_, v_hi_124_);
lean_dec_ref(v_as_120_);
return v_res_125_;
}
}
uint8_t l_Array_binSearchContains___redArg(lean_object* v_as_127_, lean_object* v_k_128_, lean_object* v_lt_129_, lean_object* v_lo_130_, lean_object* v_hi_131_){
_start:
{
lean_object* v___y_133_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_array_get_size(v_as_127_);
v___x_139_ = lean_nat_dec_lt(v_lo_130_, v___x_138_);
if (v___x_139_ == 0)
{
lean_dec(v_hi_131_);
lean_dec(v_lo_130_);
lean_dec_ref(v_lt_129_);
lean_dec(v_k_128_);
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_lt(v_hi_131_, v___x_138_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_hi_131_);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_sub(v___x_138_, v___x_141_);
v___y_133_ = v___x_142_;
goto v___jp_132_;
}
else
{
v___y_133_ = v_hi_131_;
goto v___jp_132_;
}
}
v___jp_132_:
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_le(v_lo_130_, v___y_133_);
if (v___x_134_ == 0)
{
lean_dec(v___y_133_);
lean_dec(v_lo_130_);
lean_dec_ref(v_lt_129_);
lean_dec(v_k_128_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = ((lean_object*)(l_Array_binSearchContains___redArg___closed__0));
v___x_136_ = l_Array_binSearchAux___redArg(v_lt_129_, v___x_135_, v_as_127_, v_k_128_, v_lo_130_, v___y_133_);
v___x_137_ = lean_unbox(v___x_136_);
lean_dec(v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT void l_Array_binSearchContains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_127_ = stack[0].m_obj;
lean_object* v_k_128_ = stack[1].m_obj;
lean_object* v_lt_129_ = stack[2].m_obj;
lean_object* v_lo_130_ = stack[3].m_obj;
lean_object* v_hi_131_ = stack[4].m_obj;
uint8_t v_res_143_;
v_res_143_ = l_Array_binSearchContains___redArg(v_as_127_, v_k_128_, v_lt_129_, v_lo_130_, v_hi_131_);
stack->m_num = v_res_143_;
}
LEAN_EXPORT lean_object* l_Array_binSearchContains___redArg___boxed(lean_object* v_as_144_, lean_object* v_k_145_, lean_object* v_lt_146_, lean_object* v_lo_147_, lean_object* v_hi_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Array_binSearchContains___redArg(v_as_144_, v_k_145_, v_lt_146_, v_lo_147_, v_hi_148_);
lean_dec_ref(v_as_144_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
uint8_t l_Array_binSearchContains(lean_object* v_00_u03b1_151_, lean_object* v_as_152_, lean_object* v_k_153_, lean_object* v_lt_154_, lean_object* v_lo_155_, lean_object* v_hi_156_){
_start:
{
lean_object* v___y_158_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_as_152_);
v___x_164_ = lean_nat_dec_lt(v_lo_155_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec(v_hi_156_);
lean_dec(v_lo_155_);
lean_dec_ref(v_lt_154_);
lean_dec(v_k_153_);
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_lt(v_hi_156_, v___x_163_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_hi_156_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_sub(v___x_163_, v___x_166_);
v___y_158_ = v___x_167_;
goto v___jp_157_;
}
else
{
v___y_158_ = v_hi_156_;
goto v___jp_157_;
}
}
v___jp_157_:
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_le(v_lo_155_, v___y_158_);
if (v___x_159_ == 0)
{
lean_dec(v___y_158_);
lean_dec(v_lo_155_);
lean_dec_ref(v_lt_154_);
lean_dec(v_k_153_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = ((lean_object*)(l_Array_binSearchContains___redArg___closed__0));
v___x_161_ = l_Array_binSearchAux___redArg(v_lt_154_, v___x_160_, v_as_152_, v_k_153_, v_lo_155_, v___y_158_);
v___x_162_ = lean_unbox(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT void l_Array_binSearchContains_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_152_ = stack[1].m_obj;
lean_object* v_k_153_ = stack[2].m_obj;
lean_object* v_lt_154_ = stack[3].m_obj;
lean_object* v_lo_155_ = stack[4].m_obj;
lean_object* v_hi_156_ = stack[5].m_obj;
uint8_t v_res_168_;
v_res_168_ = l_Array_binSearchContains(lean_box(0), v_as_152_, v_k_153_, v_lt_154_, v_lo_155_, v_hi_156_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Array_binSearchContains___boxed(lean_object* v_00_u03b1_169_, lean_object* v_as_170_, lean_object* v_k_171_, lean_object* v_lt_172_, lean_object* v_lo_173_, lean_object* v_hi_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Array_binSearchContains(v_00_u03b1_169_, v_as_170_, v_k_171_, v_lt_172_, v_lo_173_, v_hi_174_);
lean_dec_ref(v_as_170_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(lean_object* v_xs_x27_177_, lean_object* v_mid_178_, lean_object* v_toPure_179_, lean_object* v_v_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_array_fset(v_xs_x27_177_, v_mid_178_, v_v_180_);
v___x_182_ = lean_apply_2(v_toPure_179_, lean_box(0), v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed(lean_object* v_xs_x27_183_, lean_object* v_mid_184_, lean_object* v_toPure_185_, lean_object* v_v_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(v_xs_x27_183_, v_mid_184_, v_toPure_185_, v_v_186_);
lean_dec(v_mid_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(lean_object* v_x_188_, lean_object* v_as_189_, lean_object* v_toPure_190_, lean_object* v_v_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_j_194_; lean_object* v_as_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_add(v_x_188_, v___x_192_);
v_j_194_ = lean_array_get_size(v_as_189_);
v_as_195_ = lean_array_push(v_as_189_, v_v_191_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_193_, v_as_195_, v_j_194_);
lean_dec(v___x_193_);
v___x_197_ = lean_apply_2(v_toPure_190_, lean_box(0), v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed(lean_object* v_x_198_, lean_object* v_as_199_, lean_object* v_toPure_200_, lean_object* v_v_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(v_x_198_, v_as_199_, v_toPure_200_, v_v_201_);
lean_dec(v_x_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(lean_object* v_inst_203_, lean_object* v_lt_204_, lean_object* v_merge_205_, lean_object* v_add_206_, lean_object* v_as_207_, lean_object* v_k_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_toApplicative_211_; lean_object* v_toBind_212_; lean_object* v_toPure_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_mid_216_; lean_object* v_midVal_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_toApplicative_211_ = lean_ctor_get(v_inst_203_, 0);
v_toBind_212_ = lean_ctor_get(v_inst_203_, 1);
v_toPure_213_ = lean_ctor_get(v_toApplicative_211_, 1);
v___x_214_ = lean_nat_add(v_x_209_, v_x_210_);
v___x_215_ = lean_unsigned_to_nat(1u);
v_mid_216_ = lean_nat_shiftr(v___x_214_, v___x_215_);
lean_dec(v___x_214_);
v_midVal_217_ = lean_array_fget_borrowed(v_as_207_, v_mid_216_);
lean_inc_ref(v_lt_204_);
lean_inc(v_k_208_);
lean_inc(v_midVal_217_);
v___x_218_ = lean_apply_2(v_lt_204_, v_midVal_217_, v_k_208_);
v___x_219_ = lean_unbox(v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; uint8_t v___x_221_; 
lean_dec(v_x_210_);
lean_inc_ref(v_lt_204_);
lean_inc(v_midVal_217_);
lean_inc(v_k_208_);
v___x_220_ = lean_apply_2(v_lt_204_, v_k_208_, v_midVal_217_);
v___x_221_ = lean_unbox(v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; uint8_t v___x_223_; 
lean_inc(v_toPure_213_);
lean_inc(v_toBind_212_);
lean_dec(v_x_209_);
lean_dec(v_k_208_);
lean_dec(v_add_206_);
lean_dec_ref(v_lt_204_);
lean_dec_ref(v_inst_203_);
v___x_222_ = lean_array_get_size(v_as_207_);
v___x_223_ = lean_nat_dec_lt(v_mid_216_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
lean_dec(v_mid_216_);
lean_dec(v_toBind_212_);
lean_dec(v_merge_205_);
v___x_224_ = lean_apply_2(v_toPure_213_, lean_box(0), v_as_207_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v_xs_x27_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_inc(v_midVal_217_);
v___x_225_ = lean_box(0);
v_xs_x27_226_ = lean_array_fset(v_as_207_, v_mid_216_, v___x_225_);
v___f_227_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_227_, 0, v_xs_x27_226_);
lean_closure_set(v___f_227_, 1, v_mid_216_);
lean_closure_set(v___f_227_, 2, v_toPure_213_);
v___x_228_ = lean_apply_1(v_merge_205_, v_midVal_217_);
v___x_229_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_228_, v___f_227_);
return v___x_229_;
}
}
else
{
v_x_210_ = v_mid_216_;
goto _start;
}
}
else
{
uint8_t v___x_231_; 
v___x_231_ = lean_nat_dec_eq(v_mid_216_, v_x_209_);
if (v___x_231_ == 0)
{
lean_dec(v_x_209_);
v_x_209_ = v_mid_216_;
goto _start;
}
else
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_inc(v_toPure_213_);
lean_inc(v_toBind_212_);
lean_dec(v_mid_216_);
lean_dec(v_x_210_);
lean_dec(v_k_208_);
lean_dec(v_merge_205_);
lean_dec_ref(v_lt_204_);
lean_dec_ref(v_inst_203_);
v___f_233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_233_, 0, v_x_209_);
lean_closure_set(v___f_233_, 1, v_as_207_);
lean_closure_set(v___f_233_, 2, v_toPure_213_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_1(v_add_206_, v___x_234_);
v___x_236_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_235_, v___f_233_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux(lean_object* v_00_u03b1_237_, lean_object* v_m_238_, lean_object* v_inst_239_, lean_object* v_lt_240_, lean_object* v_merge_241_, lean_object* v_add_242_, lean_object* v_as_243_, lean_object* v_k_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(v_inst_239_, v_lt_240_, v_merge_241_, v_add_242_, v_as_243_, v_k_244_, v_x_245_, v_x_246_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___redArg(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_h__1_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_apply_4(v_h__1_252_, v_x_250_, v_x_251_, lean_box(0), lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(lean_object* v_00_u03b1_254_, lean_object* v_lt_255_, lean_object* v_as_256_, lean_object* v_k_257_, lean_object* v_motive_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_h__1_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_apply_4(v_h__1_263_, v_x_259_, v_x_260_, lean_box(0), lean_box(0));
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___boxed(lean_object* v_00_u03b1_265_, lean_object* v_lt_266_, lean_object* v_as_267_, lean_object* v_k_268_, lean_object* v_motive_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_h__1_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(v_00_u03b1_265_, v_lt_266_, v_as_267_, v_k_268_, v_motive_269_, v_x_270_, v_x_271_, v_x_272_, v_x_273_, v_h__1_274_);
lean_dec(v_k_268_);
lean_dec_ref(v_as_267_);
lean_dec_ref(v_lt_266_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__0(lean_object* v_xs_x27_276_, lean_object* v___x_277_, lean_object* v_toPure_278_, lean_object* v_v_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_array_fset(v_xs_x27_276_, v___x_277_, v_v_279_);
v___x_281_ = lean_apply_2(v_toPure_278_, lean_box(0), v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__0___boxed(lean_object* v_xs_x27_282_, lean_object* v___x_283_, lean_object* v_toPure_284_, lean_object* v_v_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Array_binInsertM___redArg___lam__0(v_xs_x27_282_, v___x_283_, v_toPure_284_, v_v_285_);
lean_dec(v___x_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__2(lean_object* v_as_287_, lean_object* v_toPure_288_, lean_object* v_v_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_array_push(v_as_287_, v_v_289_);
v___x_291_ = lean_apply_2(v_toPure_288_, lean_box(0), v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__1(lean_object* v_as_292_, lean_object* v___x_293_, lean_object* v___x_294_, lean_object* v_toPure_295_, lean_object* v_v_296_){
_start:
{
lean_object* v_as_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_as_297_ = lean_array_push(v_as_292_, v_v_296_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_293_, v_as_297_, v___x_294_);
v___x_299_ = lean_apply_2(v_toPure_295_, lean_box(0), v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__1___boxed(lean_object* v_as_300_, lean_object* v___x_301_, lean_object* v___x_302_, lean_object* v_toPure_303_, lean_object* v_v_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Array_binInsertM___redArg___lam__1(v_as_300_, v___x_301_, v___x_302_, v_toPure_303_, v_v_304_);
lean_dec(v___x_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg(lean_object* v_inst_306_, lean_object* v_lt_307_, lean_object* v_merge_308_, lean_object* v_add_309_, lean_object* v_as_310_, lean_object* v_k_311_){
_start:
{
lean_object* v_toApplicative_312_; lean_object* v_toBind_313_; lean_object* v_toPure_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_toApplicative_312_ = lean_ctor_get(v_inst_306_, 0);
v_toBind_313_ = lean_ctor_get(v_inst_306_, 1);
v_toPure_314_ = lean_ctor_get(v_toApplicative_312_, 1);
v___x_315_ = lean_array_get_size(v_as_310_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_nat_dec_eq(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_array_fget_borrowed(v_as_310_, v___x_316_);
lean_inc_ref(v_lt_307_);
lean_inc(v___x_318_);
lean_inc(v_k_311_);
v___x_319_ = lean_apply_2(v_lt_307_, v_k_311_, v___x_318_);
v___x_320_ = lean_unbox(v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
lean_inc_ref(v_lt_307_);
lean_inc(v_k_311_);
lean_inc(v___x_318_);
v___x_321_ = lean_apply_2(v_lt_307_, v___x_318_, v_k_311_);
v___x_322_ = lean_unbox(v___x_321_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; 
lean_inc(v_toPure_314_);
lean_inc(v_toBind_313_);
lean_dec(v_k_311_);
lean_dec(v_add_309_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_306_);
v___x_323_ = lean_nat_dec_lt(v___x_316_, v___x_315_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_toBind_313_);
lean_dec(v_merge_308_);
v___x_324_ = lean_apply_2(v_toPure_314_, lean_box(0), v_as_310_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v_xs_x27_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc(v___x_318_);
v___x_325_ = lean_box(0);
v_xs_x27_326_ = lean_array_fset(v_as_310_, v___x_316_, v___x_325_);
v___f_327_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_327_, 0, v_xs_x27_326_);
lean_closure_set(v___f_327_, 1, v___x_316_);
lean_closure_set(v___f_327_, 2, v_toPure_314_);
v___x_328_ = lean_apply_1(v_merge_308_, v___x_318_);
v___x_329_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_328_, v___f_327_);
return v___x_329_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_sub(v___x_315_, v___x_330_);
v___x_332_ = lean_array_fget_borrowed(v_as_310_, v___x_331_);
lean_inc_ref(v_lt_307_);
lean_inc(v_k_311_);
lean_inc(v___x_332_);
v___x_333_ = lean_apply_2(v_lt_307_, v___x_332_, v_k_311_);
v___x_334_ = lean_unbox(v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
lean_inc_ref(v_lt_307_);
lean_inc(v___x_332_);
lean_inc(v_k_311_);
v___x_335_ = lean_apply_2(v_lt_307_, v_k_311_, v___x_332_);
v___x_336_ = lean_unbox(v___x_335_);
if (v___x_336_ == 0)
{
uint8_t v___x_337_; 
lean_inc(v_toPure_314_);
lean_inc(v_toBind_313_);
lean_dec(v_k_311_);
lean_dec(v_add_309_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_306_);
v___x_337_ = lean_nat_dec_lt(v___x_331_, v___x_315_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec(v___x_331_);
lean_dec(v_toBind_313_);
lean_dec(v_merge_308_);
v___x_338_ = lean_apply_2(v_toPure_314_, lean_box(0), v_as_310_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v_xs_x27_340_; lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_inc(v___x_332_);
v___x_339_ = lean_box(0);
v_xs_x27_340_ = lean_array_fset(v_as_310_, v___x_331_, v___x_339_);
v___f_341_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_341_, 0, v_xs_x27_340_);
lean_closure_set(v___f_341_, 1, v___x_331_);
lean_closure_set(v___f_341_, 2, v_toPure_314_);
v___x_342_ = lean_apply_1(v_merge_308_, v___x_332_);
v___x_343_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_342_, v___f_341_);
return v___x_343_;
}
}
else
{
lean_object* v___x_344_; 
v___x_344_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(v_inst_306_, v_lt_307_, v_merge_308_, v_add_309_, v_as_310_, v_k_311_, v___x_316_, v___x_331_);
return v___x_344_;
}
}
else
{
lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_inc(v_toPure_314_);
lean_inc(v_toBind_313_);
lean_dec(v___x_331_);
lean_dec(v_k_311_);
lean_dec(v_merge_308_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_306_);
v___f_345_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_345_, 0, v_as_310_);
lean_closure_set(v___f_345_, 1, v_toPure_314_);
v___x_346_ = lean_box(0);
v___x_347_ = lean_apply_1(v_add_309_, v___x_346_);
v___x_348_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_347_, v___f_345_);
return v___x_348_;
}
}
}
else
{
lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc(v_toPure_314_);
lean_inc(v_toBind_313_);
lean_dec(v_k_311_);
lean_dec(v_merge_308_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_306_);
v___f_349_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_349_, 0, v_as_310_);
lean_closure_set(v___f_349_, 1, v___x_316_);
lean_closure_set(v___f_349_, 2, v___x_315_);
lean_closure_set(v___f_349_, 3, v_toPure_314_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_add_309_, v___x_350_);
v___x_352_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_351_, v___f_349_);
return v___x_352_;
}
}
else
{
lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_inc(v_toPure_314_);
lean_inc(v_toBind_313_);
lean_dec(v_k_311_);
lean_dec(v_merge_308_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_306_);
v___f_353_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_353_, 0, v_as_310_);
lean_closure_set(v___f_353_, 1, v_toPure_314_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_apply_1(v_add_309_, v___x_354_);
v___x_356_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_355_, v___f_353_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM(lean_object* v_00_u03b1_357_, lean_object* v_m_358_, lean_object* v_inst_359_, lean_object* v_lt_360_, lean_object* v_merge_361_, lean_object* v_add_362_, lean_object* v_as_363_, lean_object* v_k_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Array_binInsertM___redArg(v_inst_359_, v_lt_360_, v_merge_361_, v_add_362_, v_as_363_, v_k_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__0(lean_object* v_k_366_, lean_object* v_x_367_){
_start:
{
lean_inc(v_k_366_);
return v_k_366_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__0___boxed(lean_object* v_k_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Array_binInsert___redArg___lam__0(v_k_368_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v_k_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__1(lean_object* v_k_371_, lean_object* v_x_372_){
_start:
{
lean_inc(v_k_371_);
return v_k_371_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__1___boxed(lean_object* v_k_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Array_binInsert___redArg___lam__1(v_k_373_, v_x_374_);
lean_dec(v_k_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg(lean_object* v_lt_395_, lean_object* v_as_396_, lean_object* v_k_397_){
_start:
{
lean_object* v___f_398_; lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc_n(v_k_397_, 2);
v___f_398_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_398_, 0, v_k_397_);
v___f_399_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_399_, 0, v_k_397_);
v___x_400_ = ((lean_object*)(l_Array_binInsert___redArg___closed__9));
v___x_401_ = l_Array_binInsertM___redArg(v___x_400_, v_lt_395_, v___f_398_, v___f_399_, v_as_396_, v_k_397_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert(lean_object* v_00_u03b1_402_, lean_object* v_lt_403_, lean_object* v_as_404_, lean_object* v_k_405_){
_start:
{
lean_object* v___f_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc_n(v_k_405_, 2);
v___f_406_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_406_, 0, v_k_405_);
v___f_407_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_407_, 0, v_k_405_);
v___x_408_ = ((lean_object*)(l_Array_binInsert___redArg___closed__9));
v___x_409_ = l_Array_binInsertM___redArg(v___x_408_, v_lt_403_, v___f_406_, v___f_407_, v_as_404_, v_k_405_);
return v___x_409_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_BinSearch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_BinSearch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_BinSearch(builtin);
}
#ifdef __cplusplus
}
#endif
