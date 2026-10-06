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
LEAN_EXPORT uint8_t l_Array_binSearchContains___redArg(lean_object* v_as_127_, lean_object* v_k_128_, lean_object* v_lt_129_, lean_object* v_lo_130_, lean_object* v_hi_131_){
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
LEAN_EXPORT lean_object* l_Array_binSearchContains___redArg___boxed(lean_object* v_as_143_, lean_object* v_k_144_, lean_object* v_lt_145_, lean_object* v_lo_146_, lean_object* v_hi_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Array_binSearchContains___redArg(v_as_143_, v_k_144_, v_lt_145_, v_lo_146_, v_hi_147_);
lean_dec_ref(v_as_143_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchContains(lean_object* v_00_u03b1_150_, lean_object* v_as_151_, lean_object* v_k_152_, lean_object* v_lt_153_, lean_object* v_lo_154_, lean_object* v_hi_155_){
_start:
{
lean_object* v___y_157_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_array_get_size(v_as_151_);
v___x_163_ = lean_nat_dec_lt(v_lo_154_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v_hi_155_);
lean_dec(v_lo_154_);
lean_dec_ref(v_lt_153_);
lean_dec(v_k_152_);
return v___x_163_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_lt(v_hi_155_, v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_hi_155_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_sub(v___x_162_, v___x_165_);
v___y_157_ = v___x_166_;
goto v___jp_156_;
}
else
{
v___y_157_ = v_hi_155_;
goto v___jp_156_;
}
}
v___jp_156_:
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_le(v_lo_154_, v___y_157_);
if (v___x_158_ == 0)
{
lean_dec(v___y_157_);
lean_dec(v_lo_154_);
lean_dec_ref(v_lt_153_);
lean_dec(v_k_152_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_159_ = ((lean_object*)(l_Array_binSearchContains___redArg___closed__0));
v___x_160_ = l_Array_binSearchAux___redArg(v_lt_153_, v___x_159_, v_as_151_, v_k_152_, v_lo_154_, v___y_157_);
v___x_161_ = lean_unbox(v___x_160_);
lean_dec(v___x_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchContains___boxed(lean_object* v_00_u03b1_167_, lean_object* v_as_168_, lean_object* v_k_169_, lean_object* v_lt_170_, lean_object* v_lo_171_, lean_object* v_hi_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Array_binSearchContains(v_00_u03b1_167_, v_as_168_, v_k_169_, v_lt_170_, v_lo_171_, v_hi_172_);
lean_dec_ref(v_as_168_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(lean_object* v_xs_x27_175_, lean_object* v_mid_176_, lean_object* v_toPure_177_, lean_object* v_v_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_array_fset(v_xs_x27_175_, v_mid_176_, v_v_178_);
v___x_180_ = lean_apply_2(v_toPure_177_, lean_box(0), v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed(lean_object* v_xs_x27_181_, lean_object* v_mid_182_, lean_object* v_toPure_183_, lean_object* v_v_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(v_xs_x27_181_, v_mid_182_, v_toPure_183_, v_v_184_);
lean_dec(v_mid_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(lean_object* v_x_186_, lean_object* v_as_187_, lean_object* v_toPure_188_, lean_object* v_v_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_j_192_; lean_object* v_as_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_x_186_, v___x_190_);
v_j_192_ = lean_array_get_size(v_as_187_);
v_as_193_ = lean_array_push(v_as_187_, v_v_189_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_191_, v_as_193_, v_j_192_);
lean_dec(v___x_191_);
v___x_195_ = lean_apply_2(v_toPure_188_, lean_box(0), v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed(lean_object* v_x_196_, lean_object* v_as_197_, lean_object* v_toPure_198_, lean_object* v_v_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(v_x_196_, v_as_197_, v_toPure_198_, v_v_199_);
lean_dec(v_x_196_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(lean_object* v_inst_201_, lean_object* v_lt_202_, lean_object* v_merge_203_, lean_object* v_add_204_, lean_object* v_as_205_, lean_object* v_k_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v_toApplicative_209_; lean_object* v_toBind_210_; lean_object* v_toPure_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_mid_214_; lean_object* v_midVal_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_toApplicative_209_ = lean_ctor_get(v_inst_201_, 0);
v_toBind_210_ = lean_ctor_get(v_inst_201_, 1);
v_toPure_211_ = lean_ctor_get(v_toApplicative_209_, 1);
v___x_212_ = lean_nat_add(v_x_207_, v_x_208_);
v___x_213_ = lean_unsigned_to_nat(1u);
v_mid_214_ = lean_nat_shiftr(v___x_212_, v___x_213_);
lean_dec(v___x_212_);
v_midVal_215_ = lean_array_fget_borrowed(v_as_205_, v_mid_214_);
lean_inc_ref(v_lt_202_);
lean_inc(v_k_206_);
lean_inc(v_midVal_215_);
v___x_216_ = lean_apply_2(v_lt_202_, v_midVal_215_, v_k_206_);
v___x_217_ = lean_unbox(v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; 
lean_dec(v_x_208_);
lean_inc_ref(v_lt_202_);
lean_inc(v_midVal_215_);
lean_inc(v_k_206_);
v___x_218_ = lean_apply_2(v_lt_202_, v_k_206_, v_midVal_215_);
v___x_219_ = lean_unbox(v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; uint8_t v___x_221_; 
lean_inc(v_toPure_211_);
lean_inc(v_toBind_210_);
lean_dec(v_x_207_);
lean_dec(v_k_206_);
lean_dec(v_add_204_);
lean_dec_ref(v_lt_202_);
lean_dec_ref(v_inst_201_);
v___x_220_ = lean_array_get_size(v_as_205_);
v___x_221_ = lean_nat_dec_lt(v_mid_214_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec(v_mid_214_);
lean_dec(v_toBind_210_);
lean_dec(v_merge_203_);
v___x_222_ = lean_apply_2(v_toPure_211_, lean_box(0), v_as_205_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v_xs_x27_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_inc(v_midVal_215_);
v___x_223_ = lean_box(0);
v_xs_x27_224_ = lean_array_fset(v_as_205_, v_mid_214_, v___x_223_);
v___f_225_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_225_, 0, v_xs_x27_224_);
lean_closure_set(v___f_225_, 1, v_mid_214_);
lean_closure_set(v___f_225_, 2, v_toPure_211_);
v___x_226_ = lean_apply_1(v_merge_203_, v_midVal_215_);
v___x_227_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v___x_226_, v___f_225_);
return v___x_227_;
}
}
else
{
v_x_208_ = v_mid_214_;
goto _start;
}
}
else
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_eq(v_mid_214_, v_x_207_);
if (v___x_229_ == 0)
{
lean_dec(v_x_207_);
v_x_207_ = v_mid_214_;
goto _start;
}
else
{
lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc(v_toPure_211_);
lean_inc(v_toBind_210_);
lean_dec(v_mid_214_);
lean_dec(v_x_208_);
lean_dec(v_k_206_);
lean_dec(v_merge_203_);
lean_dec_ref(v_lt_202_);
lean_dec_ref(v_inst_201_);
v___f_231_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_231_, 0, v_x_207_);
lean_closure_set(v___f_231_, 1, v_as_205_);
lean_closure_set(v___f_231_, 2, v_toPure_211_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_add_204_, v___x_232_);
v___x_234_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v___x_233_, v___f_231_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux(lean_object* v_00_u03b1_235_, lean_object* v_m_236_, lean_object* v_inst_237_, lean_object* v_lt_238_, lean_object* v_merge_239_, lean_object* v_add_240_, lean_object* v_as_241_, lean_object* v_k_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(v_inst_237_, v_lt_238_, v_merge_239_, v_add_240_, v_as_241_, v_k_242_, v_x_243_, v_x_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_h__1_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_apply_4(v_h__1_250_, v_x_248_, v_x_249_, lean_box(0), lean_box(0));
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(lean_object* v_00_u03b1_252_, lean_object* v_lt_253_, lean_object* v_as_254_, lean_object* v_k_255_, lean_object* v_motive_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_h__1_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_apply_4(v_h__1_261_, v_x_257_, v_x_258_, lean_box(0), lean_box(0));
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___boxed(lean_object* v_00_u03b1_263_, lean_object* v_lt_264_, lean_object* v_as_265_, lean_object* v_k_266_, lean_object* v_motive_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_h__1_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(v_00_u03b1_263_, v_lt_264_, v_as_265_, v_k_266_, v_motive_267_, v_x_268_, v_x_269_, v_x_270_, v_x_271_, v_h__1_272_);
lean_dec(v_k_266_);
lean_dec_ref(v_as_265_);
lean_dec_ref(v_lt_264_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__0(lean_object* v_xs_x27_274_, lean_object* v___x_275_, lean_object* v_toPure_276_, lean_object* v_v_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_array_fset(v_xs_x27_274_, v___x_275_, v_v_277_);
v___x_279_ = lean_apply_2(v_toPure_276_, lean_box(0), v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__0___boxed(lean_object* v_xs_x27_280_, lean_object* v___x_281_, lean_object* v_toPure_282_, lean_object* v_v_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Array_binInsertM___redArg___lam__0(v_xs_x27_280_, v___x_281_, v_toPure_282_, v_v_283_);
lean_dec(v___x_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__2(lean_object* v_as_285_, lean_object* v_toPure_286_, lean_object* v_v_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_array_push(v_as_285_, v_v_287_);
v___x_289_ = lean_apply_2(v_toPure_286_, lean_box(0), v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__1(lean_object* v_as_290_, lean_object* v___x_291_, lean_object* v___x_292_, lean_object* v_toPure_293_, lean_object* v_v_294_){
_start:
{
lean_object* v_as_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_as_295_ = lean_array_push(v_as_290_, v_v_294_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_291_, v_as_295_, v___x_292_);
v___x_297_ = lean_apply_2(v_toPure_293_, lean_box(0), v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg___lam__1___boxed(lean_object* v_as_298_, lean_object* v___x_299_, lean_object* v___x_300_, lean_object* v_toPure_301_, lean_object* v_v_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Array_binInsertM___redArg___lam__1(v_as_298_, v___x_299_, v___x_300_, v_toPure_301_, v_v_302_);
lean_dec(v___x_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___redArg(lean_object* v_inst_304_, lean_object* v_lt_305_, lean_object* v_merge_306_, lean_object* v_add_307_, lean_object* v_as_308_, lean_object* v_k_309_){
_start:
{
lean_object* v_toApplicative_310_; lean_object* v_toBind_311_; lean_object* v_toPure_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_toApplicative_310_ = lean_ctor_get(v_inst_304_, 0);
v_toBind_311_ = lean_ctor_get(v_inst_304_, 1);
v_toPure_312_ = lean_ctor_get(v_toApplicative_310_, 1);
v___x_313_ = lean_array_get_size(v_as_308_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_array_fget_borrowed(v_as_308_, v___x_314_);
lean_inc_ref(v_lt_305_);
lean_inc(v___x_316_);
lean_inc(v_k_309_);
v___x_317_ = lean_apply_2(v_lt_305_, v_k_309_, v___x_316_);
v___x_318_ = lean_unbox(v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
lean_inc_ref(v_lt_305_);
lean_inc(v_k_309_);
lean_inc(v___x_316_);
v___x_319_ = lean_apply_2(v_lt_305_, v___x_316_, v_k_309_);
v___x_320_ = lean_unbox(v___x_319_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
lean_inc(v_toPure_312_);
lean_inc(v_toBind_311_);
lean_dec(v_k_309_);
lean_dec(v_add_307_);
lean_dec_ref(v_lt_305_);
lean_dec_ref(v_inst_304_);
v___x_321_ = lean_nat_dec_lt(v___x_314_, v___x_313_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_toBind_311_);
lean_dec(v_merge_306_);
v___x_322_ = lean_apply_2(v_toPure_312_, lean_box(0), v_as_308_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v_xs_x27_324_; lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc(v___x_316_);
v___x_323_ = lean_box(0);
v_xs_x27_324_ = lean_array_fset(v_as_308_, v___x_314_, v___x_323_);
v___f_325_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_325_, 0, v_xs_x27_324_);
lean_closure_set(v___f_325_, 1, v___x_314_);
lean_closure_set(v___f_325_, 2, v_toPure_312_);
v___x_326_ = lean_apply_1(v_merge_306_, v___x_316_);
v___x_327_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_326_, v___f_325_);
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_sub(v___x_313_, v___x_328_);
v___x_330_ = lean_array_fget_borrowed(v_as_308_, v___x_329_);
lean_inc_ref(v_lt_305_);
lean_inc(v_k_309_);
lean_inc(v___x_330_);
v___x_331_ = lean_apply_2(v_lt_305_, v___x_330_, v_k_309_);
v___x_332_ = lean_unbox(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
lean_inc_ref(v_lt_305_);
lean_inc(v___x_330_);
lean_inc(v_k_309_);
v___x_333_ = lean_apply_2(v_lt_305_, v_k_309_, v___x_330_);
v___x_334_ = lean_unbox(v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
lean_inc(v_toPure_312_);
lean_inc(v_toBind_311_);
lean_dec(v_k_309_);
lean_dec(v_add_307_);
lean_dec_ref(v_lt_305_);
lean_dec_ref(v_inst_304_);
v___x_335_ = lean_nat_dec_lt(v___x_329_, v___x_313_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v___x_329_);
lean_dec(v_toBind_311_);
lean_dec(v_merge_306_);
v___x_336_ = lean_apply_2(v_toPure_312_, lean_box(0), v_as_308_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v_xs_x27_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_inc(v___x_330_);
v___x_337_ = lean_box(0);
v_xs_x27_338_ = lean_array_fset(v_as_308_, v___x_329_, v___x_337_);
v___f_339_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_339_, 0, v_xs_x27_338_);
lean_closure_set(v___f_339_, 1, v___x_329_);
lean_closure_set(v___f_339_, 2, v_toPure_312_);
v___x_340_ = lean_apply_1(v_merge_306_, v___x_330_);
v___x_341_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_340_, v___f_339_);
return v___x_341_;
}
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(v_inst_304_, v_lt_305_, v_merge_306_, v_add_307_, v_as_308_, v_k_309_, v___x_314_, v___x_329_);
return v___x_342_;
}
}
else
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc(v_toPure_312_);
lean_inc(v_toBind_311_);
lean_dec(v___x_329_);
lean_dec(v_k_309_);
lean_dec(v_merge_306_);
lean_dec_ref(v_lt_305_);
lean_dec_ref(v_inst_304_);
v___f_343_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_343_, 0, v_as_308_);
lean_closure_set(v___f_343_, 1, v_toPure_312_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_apply_1(v_add_307_, v___x_344_);
v___x_346_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_345_, v___f_343_);
return v___x_346_;
}
}
}
else
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_inc(v_toPure_312_);
lean_inc(v_toBind_311_);
lean_dec(v_k_309_);
lean_dec(v_merge_306_);
lean_dec_ref(v_lt_305_);
lean_dec_ref(v_inst_304_);
v___f_347_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_347_, 0, v_as_308_);
lean_closure_set(v___f_347_, 1, v___x_314_);
lean_closure_set(v___f_347_, 2, v___x_313_);
lean_closure_set(v___f_347_, 3, v_toPure_312_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_apply_1(v_add_307_, v___x_348_);
v___x_350_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_349_, v___f_347_);
return v___x_350_;
}
}
else
{
lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_inc(v_toPure_312_);
lean_inc(v_toBind_311_);
lean_dec(v_k_309_);
lean_dec(v_merge_306_);
lean_dec_ref(v_lt_305_);
lean_dec_ref(v_inst_304_);
v___f_351_ = lean_alloc_closure((void*)(l_Array_binInsertM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_351_, 0, v_as_308_);
lean_closure_set(v___f_351_, 1, v_toPure_312_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_apply_1(v_add_307_, v___x_352_);
v___x_354_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_353_, v___f_351_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM(lean_object* v_00_u03b1_355_, lean_object* v_m_356_, lean_object* v_inst_357_, lean_object* v_lt_358_, lean_object* v_merge_359_, lean_object* v_add_360_, lean_object* v_as_361_, lean_object* v_k_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Array_binInsertM___redArg(v_inst_357_, v_lt_358_, v_merge_359_, v_add_360_, v_as_361_, v_k_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__0(lean_object* v_k_364_, lean_object* v_x_365_){
_start:
{
lean_inc(v_k_364_);
return v_k_364_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__0___boxed(lean_object* v_k_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Array_binInsert___redArg___lam__0(v_k_366_, v_x_367_);
lean_dec(v_x_367_);
lean_dec(v_k_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__1(lean_object* v_k_369_, lean_object* v_x_370_){
_start:
{
lean_inc(v_k_369_);
return v_k_369_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg___lam__1___boxed(lean_object* v_k_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Array_binInsert___redArg___lam__1(v_k_371_, v_x_372_);
lean_dec(v_k_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___redArg(lean_object* v_lt_393_, lean_object* v_as_394_, lean_object* v_k_395_){
_start:
{
lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc_n(v_k_395_, 2);
v___f_396_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_396_, 0, v_k_395_);
v___f_397_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_397_, 0, v_k_395_);
v___x_398_ = ((lean_object*)(l_Array_binInsert___redArg___closed__9));
v___x_399_ = l_Array_binInsertM___redArg(v___x_398_, v_lt_393_, v___f_396_, v___f_397_, v_as_394_, v_k_395_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert(lean_object* v_00_u03b1_400_, lean_object* v_lt_401_, lean_object* v_as_402_, lean_object* v_k_403_){
_start:
{
lean_object* v___f_404_; lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc_n(v_k_403_, 2);
v___f_404_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_404_, 0, v_k_403_);
v___f_405_ = lean_alloc_closure((void*)(l_Array_binInsert___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_405_, 0, v_k_403_);
v___x_406_ = ((lean_object*)(l_Array_binInsert___redArg___closed__9));
v___x_407_ = l_Array_binInsertM___redArg(v___x_406_, v_lt_401_, v___f_404_, v___f_405_, v_as_402_, v_k_403_);
return v___x_407_;
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
