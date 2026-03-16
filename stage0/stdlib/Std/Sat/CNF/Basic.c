// Lean compiler output
// Module: Std.Sat.CNF.Basic
// Imports: public import Std.Sat.CNF.Literal public import Init.Data.Prod public import Init.Data.Array.Lemmas
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_CNF_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_CNF_empty___closed__0 = (const lean_object*)&l_Std_Sat_CNF_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_CNF_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_CNF_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Sat_CNF_instAppend___closed__0 = (const lean_object*)&l_Std_Sat_CNF_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object*);
static lean_once_cell_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value;
static const lean_ctor_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value)}};
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value;
static const lean_ctor_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value)}};
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value;
static const lean_ctor_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value)}};
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9_value;
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg___lam__0(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_fst_3_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_x_2_);
v___x_5_ = lean_apply_1(v_a_1_, v_fst_3_);
v___x_6_ = lean_unbox(v___x_5_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_snd_4_);
lean_dec(v_snd_4_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
v___x_8_ = 1;
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = lean_unbox(v___x_5_);
return v___x_9_;
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = lean_unbox(v_snd_4_);
lean_dec(v_snd_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___lam__0___boxed(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_Sat_CNF_Clause_eval___redArg___lam__0(v_a_11_, v_x_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object* v_a_15_, lean_object* v_c_16_){
_start:
{
lean_object* v___f_17_; uint8_t v___x_18_; 
v___f_17_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_eval___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_17_, 0, v_a_15_);
v___x_18_ = l_List_any___redArg(v_c_16_, v___f_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object* v_a_19_, lean_object* v_c_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_19_, v_c_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object* v_00_u03b1_23_, lean_object* v_a_24_, lean_object* v_c_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_24_, v_c_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object* v_00_u03b1_27_, lean_object* v_a_28_, lean_object* v_c_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_Sat_CNF_Clause_eval(v_00_u03b1_27_, v_a_28_, v_c_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object* v_a_32_, lean_object* v_as_33_, size_t v_i_34_, size_t v_stop_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_usize_dec_eq(v_i_34_, v_stop_35_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_37_ = 1;
v___x_38_ = lean_array_uget_borrowed(v_as_33_, v_i_34_);
lean_inc(v___x_38_);
lean_inc_ref(v_a_32_);
v___x_39_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_32_, v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v_a_32_);
return v___x_37_;
}
else
{
if (v___x_36_ == 0)
{
size_t v___x_40_; size_t v___x_41_; 
v___x_40_ = ((size_t)1ULL);
v___x_41_ = lean_usize_add(v_i_34_, v___x_40_);
v_i_34_ = v___x_41_;
goto _start;
}
else
{
lean_dec_ref(v_a_32_);
return v___x_37_;
}
}
}
else
{
uint8_t v___x_43_; 
lean_dec_ref(v_a_32_);
v___x_43_ = 0;
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object* v_a_44_, lean_object* v_as_45_, lean_object* v_i_46_, lean_object* v_stop_47_){
_start:
{
size_t v_i_boxed_48_; size_t v_stop_boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_i_boxed_48_ = lean_unbox_usize(v_i_46_);
lean_dec(v_i_46_);
v_stop_boxed_49_ = lean_unbox_usize(v_stop_47_);
lean_dec(v_stop_47_);
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_44_, v_as_45_, v_i_boxed_48_, v_stop_boxed_49_);
lean_dec_ref(v_as_45_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object* v_a_52_, lean_object* v_f_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_array_get_size(v_f_53_);
v___x_56_ = lean_nat_dec_lt(v___x_54_, v___x_55_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
lean_dec_ref(v_a_52_);
v___x_57_ = 1;
return v___x_57_;
}
else
{
if (v___x_56_ == 0)
{
lean_dec_ref(v_a_52_);
return v___x_56_;
}
else
{
size_t v___x_58_; size_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_55_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_52_, v_f_53_, v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
return v___x_56_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object* v_a_62_, lean_object* v_f_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Std_Sat_CNF_eval___redArg(v_a_62_, v_f_63_);
lean_dec_ref(v_f_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object* v_00_u03b1_66_, lean_object* v_a_67_, lean_object* v_f_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Std_Sat_CNF_eval___redArg(v_a_67_, v_f_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object* v_00_u03b1_70_, lean_object* v_a_71_, lean_object* v_f_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Sat_CNF_eval(v_00_u03b1_70_, v_a_71_, v_f_72_);
lean_dec_ref(v_f_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object* v_00_u03b1_75_, lean_object* v_a_76_, lean_object* v_as_77_, size_t v_i_78_, size_t v_stop_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_76_, v_as_77_, v_i_78_, v_stop_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object* v_00_u03b1_81_, lean_object* v_a_82_, lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(v_00_u03b1_81_, v_a_82_, v_as_83_, v_i_boxed_86_, v_stop_boxed_87_);
lean_dec_ref(v_as_83_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object* v_00_u03b1_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = ((lean_object*)(l_Std_Sat_CNF_empty___closed__0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object* v_n_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_mk_empty_array_with_capacity(v_n_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object* v_n_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_96_);
lean_dec(v_n_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object* v_00_u03b1_98_, lean_object* v_n_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_mk_empty_array_with_capacity(v_n_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object* v_00_u03b1_101_, lean_object* v_n_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_101_, v_n_102_);
lean_dec(v_n_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object* v_c_104_, lean_object* v_f_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_array_push(v_f_105_, v_c_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object* v_00_u03b1_107_, lean_object* v_c_108_, lean_object* v_f_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_array_push(v_f_109_, v_c_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object* v_f1_111_, lean_object* v_f2_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Array_append___redArg(v_f1_111_, v_f2_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object* v_f1_114_, lean_object* v_f2_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Sat_CNF_append___redArg(v_f1_114_, v_f2_115_);
lean_dec_ref(v_f2_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object* v_00_u03b1_117_, lean_object* v_f1_118_, lean_object* v_f2_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Array_append___redArg(v_f1_118_, v_f2_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object* v_00_u03b1_121_, lean_object* v_f1_122_, lean_object* v_f2_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Sat_CNF_append(v_00_u03b1_121_, v_f1_122_, v_f2_123_);
lean_dec_ref(v_f2_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object* v_00_u03b1_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___closed__0));
return v___x_127_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___f_129_; 
v___x_128_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_129_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_129_, 0, v___x_128_);
return v___f_129_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object* v_v_130_, lean_object* v_c_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___f_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___f_133_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_133_, 0, v_inst_132_);
v___f_134_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0, &l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0_once, _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0);
v___f_135_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_135_, 0, v___f_133_);
lean_closure_set(v___f_135_, 1, v___f_134_);
v___x_136_ = 0;
v___x_137_ = lean_box(v___x_136_);
lean_inc(v_v_130_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_v_130_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
lean_inc(v_c_131_);
lean_inc_ref(v___f_135_);
v___x_139_ = l_List_elem___redArg(v___f_135_, v___x_138_, v_c_131_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = 1;
v___x_141_ = lean_box(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_v_130_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = l_List_elem___redArg(v___f_135_, v___x_142_, v_c_131_);
return v___x_143_;
}
else
{
lean_dec_ref(v___f_135_);
lean_dec(v_c_131_);
lean_dec(v_v_130_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* v_v_144_, lean_object* v_c_145_, lean_object* v_inst_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(v_v_144_, v_c_145_, v_inst_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object* v_00_u03b1_149_, lean_object* v_v_150_, lean_object* v_c_151_, lean_object* v_inst_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(v_v_150_, v_c_151_, v_inst_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object* v_00_u03b1_154_, lean_object* v_v_155_, lean_object* v_c_156_, lean_object* v_inst_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(v_00_u03b1_154_, v_v_155_, v_c_156_, v_inst_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object* v_00_u03b1_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object* v_c_162_, lean_object* v_f_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___f_165_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_165_, 0, v_inst_164_);
v___f_166_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0, &l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0_once, _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0);
v___f_167_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_167_, 0, v___f_165_);
lean_closure_set(v___f_167_, 1, v___f_166_);
v___x_168_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_168_, 0, lean_box(0));
lean_closure_set(v___x_168_, 1, v___f_167_);
v___x_169_ = l_Array_contains___redArg(v___x_168_, v_f_163_, v_c_162_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object* v_c_170_, lean_object* v_f_171_, lean_object* v_inst_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_170_, v_f_171_, v_inst_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object* v_00_u03b1_175_, lean_object* v_c_176_, lean_object* v_f_177_, lean_object* v_inst_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_176_, v_f_177_, v_inst_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object* v_00_u03b1_180_, lean_object* v_c_181_, lean_object* v_f_182_, lean_object* v_inst_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(v_00_u03b1_180_, v_c_181_, v_f_182_, v_inst_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(lean_object* v_v_186_, lean_object* v_inst_187_, lean_object* v_a_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(v_v_186_, v_a_188_, v_inst_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v_v_190_, lean_object* v_inst_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(v_v_190_, v_inst_191_, v_a_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_195_, lean_object* v_f_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; uint8_t v___x_199_; 
v___f_198_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_198_, 0, v_v_195_);
lean_closure_set(v___f_198_, 1, v_inst_197_);
v___x_199_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_f_196_, v___f_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_200_, lean_object* v_f_201_, lean_object* v_inst_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_200_, v_f_201_, v_inst_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_205_, lean_object* v_v_206_, lean_object* v_f_207_, lean_object* v_inst_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_206_, v_f_207_, v_inst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_210_, lean_object* v_v_211_, lean_object* v_f_212_, lean_object* v_inst_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(v_00_u03b1_210_, v_v_211_, v_f_212_, v_inst_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t v___x_216_, lean_object* v_x_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = l_List_isEmpty___redArg(v_x_217_);
if (v___x_218_ == 0)
{
return v___x_216_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v___x_220_, lean_object* v_x_221_){
_start:
{
uint8_t v___x_86__boxed_222_; uint8_t v_res_223_; lean_object* v_r_224_; 
v___x_86__boxed_222_ = lean_unbox(v___x_220_);
v_res_223_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v___x_86__boxed_222_, v_x_221_);
lean_dec(v_x_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object* v_f_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_array_get_size(v_f_244_);
v___x_247_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9));
v___x_248_ = lean_nat_dec_lt(v___x_245_, v___x_246_);
if (v___x_248_ == 0)
{
lean_dec_ref(v_f_244_);
return v___x_248_;
}
else
{
if (v___x_248_ == 0)
{
lean_dec_ref(v_f_244_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___f_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_249_ = lean_box(v___x_248_);
v___f_250_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_250_, 0, v___x_249_);
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_246_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_247_, v___f_250_, v_f_244_, v___x_251_, v___x_252_);
v___x_254_ = lean_unbox(v___x_253_);
lean_dec(v___x_253_);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object* v_f_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object* v_00_u03b1_258_, lean_object* v_f_259_, lean_object* v_inst_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_262_, lean_object* v_f_263_, lean_object* v_inst_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(v_00_u03b1_262_, v_f_263_, v_inst_264_);
lean_dec_ref(v_inst_264_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Literal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_CNF_Literal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Literal(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Literal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
