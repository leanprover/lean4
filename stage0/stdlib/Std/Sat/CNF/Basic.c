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
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
lean_dec_ref(v_a_1_);
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_5_);
lean_dec_ref(v_x_2_);
v_fst_6_ = lean_ctor_get(v_head_4_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_head_4_, 1);
lean_inc(v_snd_7_);
lean_dec(v_head_4_);
lean_inc_ref(v_a_1_);
v___x_8_ = lean_apply_1(v_a_1_, v_fst_6_);
v___x_9_ = lean_unbox(v___x_8_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lean_unbox(v_snd_7_);
lean_dec(v_snd_7_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
lean_dec(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_11_ = 1;
return v___x_11_;
}
else
{
v_x_2_ = v_tail_5_;
goto _start;
}
}
else
{
uint8_t v___x_13_; 
v___x_13_ = lean_unbox(v_snd_7_);
if (v___x_13_ == 0)
{
lean_dec(v_snd_7_);
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
uint8_t v___x_15_; 
lean_dec(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_15_ = lean_unbox(v_snd_7_);
lean_dec(v_snd_7_);
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_16_, v_x_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object* v_a_20_, lean_object* v_c_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_20_, v_c_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object* v_a_23_, lean_object* v_c_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_23_, v_c_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object* v_00_u03b1_27_, lean_object* v_a_28_, lean_object* v_c_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_28_, v_c_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object* v_00_u03b1_31_, lean_object* v_a_32_, lean_object* v_c_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Sat_CNF_Clause_eval(v_00_u03b1_31_, v_a_32_, v_c_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_object* v_00_u03b1_36_, lean_object* v_a_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_37_, v_x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(lean_object* v_00_u03b1_40_, lean_object* v_a_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(v_00_u03b1_40_, v_a_41_, v_x_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object* v_a_45_, lean_object* v_as_46_, size_t v_i_47_, size_t v_stop_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_usize_dec_eq(v_i_47_, v_stop_48_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_50_ = 1;
v___x_51_ = lean_array_uget_borrowed(v_as_46_, v_i_47_);
lean_inc(v___x_51_);
lean_inc_ref(v_a_45_);
v___x_52_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_45_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v_a_45_);
return v___x_50_;
}
else
{
if (v___x_49_ == 0)
{
size_t v___x_53_; size_t v___x_54_; 
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_add(v_i_47_, v___x_53_);
v_i_47_ = v___x_54_;
goto _start;
}
else
{
lean_dec_ref(v_a_45_);
return v___x_50_;
}
}
}
else
{
uint8_t v___x_56_; 
lean_dec_ref(v_a_45_);
v___x_56_ = 0;
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object* v_a_57_, lean_object* v_as_58_, lean_object* v_i_59_, lean_object* v_stop_60_){
_start:
{
size_t v_i_boxed_61_; size_t v_stop_boxed_62_; uint8_t v_res_63_; lean_object* v_r_64_; 
v_i_boxed_61_ = lean_unbox_usize(v_i_59_);
lean_dec(v_i_59_);
v_stop_boxed_62_ = lean_unbox_usize(v_stop_60_);
lean_dec(v_stop_60_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_57_, v_as_58_, v_i_boxed_61_, v_stop_boxed_62_);
lean_dec_ref(v_as_58_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object* v_a_65_, lean_object* v_f_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_array_get_size(v_f_66_);
v___x_69_ = lean_nat_dec_lt(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
lean_dec_ref(v_a_65_);
v___x_70_ = 1;
return v___x_70_;
}
else
{
if (v___x_69_ == 0)
{
lean_dec_ref(v_a_65_);
return v___x_69_;
}
else
{
size_t v___x_71_; size_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = ((size_t)0ULL);
v___x_72_ = lean_usize_of_nat(v___x_68_);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_65_, v_f_66_, v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
return v___x_69_;
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object* v_a_75_, lean_object* v_f_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Std_Sat_CNF_eval___redArg(v_a_75_, v_f_76_);
lean_dec_ref(v_f_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object* v_00_u03b1_79_, lean_object* v_a_80_, lean_object* v_f_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = l_Std_Sat_CNF_eval___redArg(v_a_80_, v_f_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object* v_00_u03b1_83_, lean_object* v_a_84_, lean_object* v_f_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Sat_CNF_eval(v_00_u03b1_83_, v_a_84_, v_f_85_);
lean_dec_ref(v_f_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object* v_00_u03b1_88_, lean_object* v_a_89_, lean_object* v_as_90_, size_t v_i_91_, size_t v_stop_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_89_, v_as_90_, v_i_91_, v_stop_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object* v_00_u03b1_94_, lean_object* v_a_95_, lean_object* v_as_96_, lean_object* v_i_97_, lean_object* v_stop_98_){
_start:
{
size_t v_i_boxed_99_; size_t v_stop_boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_i_boxed_99_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_stop_boxed_100_ = lean_unbox_usize(v_stop_98_);
lean_dec(v_stop_98_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(v_00_u03b1_94_, v_a_95_, v_as_96_, v_i_boxed_99_, v_stop_boxed_100_);
lean_dec_ref(v_as_96_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object* v_00_u03b1_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l_Std_Sat_CNF_empty___closed__0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object* v_n_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_mk_empty_array_with_capacity(v_n_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object* v_n_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_109_);
lean_dec(v_n_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object* v_00_u03b1_111_, lean_object* v_n_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_mk_empty_array_with_capacity(v_n_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object* v_00_u03b1_114_, lean_object* v_n_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_114_, v_n_115_);
lean_dec(v_n_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object* v_c_117_, lean_object* v_f_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_array_push(v_f_118_, v_c_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object* v_00_u03b1_120_, lean_object* v_c_121_, lean_object* v_f_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_array_push(v_f_122_, v_c_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object* v_f1_124_, lean_object* v_f2_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Array_append___redArg(v_f1_124_, v_f2_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object* v_f1_127_, lean_object* v_f2_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_Sat_CNF_append___redArg(v_f1_127_, v_f2_128_);
lean_dec_ref(v_f2_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object* v_00_u03b1_130_, lean_object* v_f1_131_, lean_object* v_f2_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Array_append___redArg(v_f1_131_, v_f2_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object* v_00_u03b1_134_, lean_object* v_f1_135_, lean_object* v_f2_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Sat_CNF_append(v_00_u03b1_134_, v_f1_135_, v_f2_136_);
lean_dec_ref(v_f2_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object* v_00_u03b1_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___closed__0));
return v___x_140_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; lean_object* v___f_142_; 
v___x_141_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_142_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_142_, 0, v___x_141_);
return v___f_142_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(lean_object* v_v_143_, lean_object* v_c_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___f_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___f_146_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_146_, 0, v_inst_145_);
v___f_147_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0, &l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once, _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0);
v___f_148_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_148_, 0, v___f_146_);
lean_closure_set(v___f_148_, 1, v___f_147_);
v___x_149_ = 0;
v___x_150_ = lean_box(v___x_149_);
lean_inc(v_v_143_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_v_143_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_inc(v_c_144_);
lean_inc_ref(v___f_148_);
v___x_152_ = l_List_elem___redArg(v___f_148_, v___x_151_, v_c_144_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_153_ = 1;
v___x_154_ = lean_box(v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_v_143_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = l_List_elem___redArg(v___f_148_, v___x_155_, v_c_144_);
return v___x_156_;
}
else
{
lean_dec_ref(v___f_148_);
lean_dec(v_c_144_);
lean_dec(v_v_143_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___boxed(lean_object* v_v_157_, lean_object* v_c_158_, lean_object* v_inst_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_157_, v_c_158_, v_inst_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(lean_object* v_00_u03b1_162_, lean_object* v_v_163_, lean_object* v_c_164_, lean_object* v_inst_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_163_, v_c_164_, v_inst_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___boxed(lean_object* v_00_u03b1_167_, lean_object* v_v_168_, lean_object* v_c_169_, lean_object* v_inst_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(v_00_u03b1_167_, v_v_168_, v_c_169_, v_inst_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object* v_v_173_, lean_object* v_c_174_, lean_object* v_inst_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_173_, v_c_174_, v_inst_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* v_v_177_, lean_object* v_c_178_, lean_object* v_inst_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(v_v_177_, v_c_178_, v_inst_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object* v_00_u03b1_182_, lean_object* v_v_183_, lean_object* v_c_184_, lean_object* v_inst_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_183_, v_c_184_, v_inst_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object* v_00_u03b1_187_, lean_object* v_v_188_, lean_object* v_c_189_, lean_object* v_inst_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(v_00_u03b1_187_, v_v_188_, v_c_189_, v_inst_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object* v_00_u03b1_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(lean_object* v_c_195_, lean_object* v_f_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___f_198_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_198_, 0, v_inst_197_);
v___f_199_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0, &l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once, _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0);
v___f_200_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_200_, 0, v___f_198_);
lean_closure_set(v___f_200_, 1, v___f_199_);
v___x_201_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_201_, 0, lean_box(0));
lean_closure_set(v___x_201_, 1, v___f_200_);
v___x_202_ = l_Array_contains___redArg(v___x_201_, v_f_196_, v_c_195_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg___boxed(lean_object* v_c_203_, lean_object* v_f_204_, lean_object* v_inst_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_203_, v_f_204_, v_inst_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(lean_object* v_00_u03b1_208_, lean_object* v_c_209_, lean_object* v_f_210_, lean_object* v_inst_211_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_209_, v_f_210_, v_inst_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___boxed(lean_object* v_00_u03b1_213_, lean_object* v_c_214_, lean_object* v_f_215_, lean_object* v_inst_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(v_00_u03b1_213_, v_c_214_, v_f_215_, v_inst_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object* v_c_219_, lean_object* v_f_220_, lean_object* v_inst_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_219_, v_f_220_, v_inst_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object* v_c_223_, lean_object* v_f_224_, lean_object* v_inst_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_223_, v_f_224_, v_inst_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object* v_00_u03b1_228_, lean_object* v_c_229_, lean_object* v_f_230_, lean_object* v_inst_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_229_, v_f_230_, v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object* v_00_u03b1_233_, lean_object* v_c_234_, lean_object* v_f_235_, lean_object* v_inst_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(v_00_u03b1_233_, v_c_234_, v_f_235_, v_inst_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(lean_object* v_v_239_, lean_object* v_inst_240_, lean_object* v_a_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_239_, v_a_241_, v_inst_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed(lean_object* v_v_243_, lean_object* v_inst_244_, lean_object* v_a_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(v_v_243_, v_inst_244_, v_a_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(lean_object* v_v_248_, lean_object* v_f_249_, lean_object* v_inst_250_){
_start:
{
lean_object* v___f_251_; uint8_t v___x_252_; 
v___f_251_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_251_, 0, v_v_248_);
lean_closure_set(v___f_251_, 1, v_inst_250_);
v___x_252_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_f_249_, v___f_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___boxed(lean_object* v_v_253_, lean_object* v_f_254_, lean_object* v_inst_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_253_, v_f_254_, v_inst_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(lean_object* v_00_u03b1_258_, lean_object* v_v_259_, lean_object* v_f_260_, lean_object* v_inst_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_259_, v_f_260_, v_inst_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___boxed(lean_object* v_00_u03b1_263_, lean_object* v_v_264_, lean_object* v_f_265_, lean_object* v_inst_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(v_00_u03b1_263_, v_v_264_, v_f_265_, v_inst_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_269_, lean_object* v_f_270_, lean_object* v_inst_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_269_, v_f_270_, v_inst_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_273_, lean_object* v_f_274_, lean_object* v_inst_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_273_, v_f_274_, v_inst_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_278_, lean_object* v_v_279_, lean_object* v_f_280_, lean_object* v_inst_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_279_, v_f_280_, v_inst_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_283_, lean_object* v_v_284_, lean_object* v_f_285_, lean_object* v_inst_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(v_00_u03b1_283_, v_v_284_, v_f_285_, v_inst_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t v___x_289_, lean_object* v_x_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_List_isEmpty___redArg(v_x_290_);
if (v___x_291_ == 0)
{
return v___x_289_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v___x_293_, lean_object* v_x_294_){
_start:
{
uint8_t v___x_86__boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v___x_86__boxed_295_ = lean_unbox(v___x_293_);
v_res_296_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v___x_86__boxed_295_, v_x_294_);
lean_dec(v_x_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object* v_f_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_array_get_size(v_f_317_);
v___x_320_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9));
v___x_321_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_321_ == 0)
{
lean_dec_ref(v_f_317_);
return v___x_321_;
}
else
{
if (v___x_321_ == 0)
{
lean_dec_ref(v_f_317_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___f_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_322_ = lean_box(v___x_321_);
v___f_323_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_323_, 0, v___x_322_);
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_319_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_320_, v___f_323_, v_f_317_, v___x_324_, v___x_325_);
v___x_327_ = lean_unbox(v___x_326_);
lean_dec(v___x_326_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object* v_f_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object* v_00_u03b1_331_, lean_object* v_f_332_, lean_object* v_inst_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_335_, lean_object* v_f_336_, lean_object* v_inst_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(v_00_u03b1_335_, v_f_336_, v_inst_337_);
lean_dec_ref(v_inst_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
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
