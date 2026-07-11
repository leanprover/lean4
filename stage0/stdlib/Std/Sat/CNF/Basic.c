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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object*);
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
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__10 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__10_value;
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
lean_dec_ref_known(v_x_2_, 2);
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
lean_object* v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; 
v___x_50_ = lean_array_uget_borrowed(v_as_46_, v_i_47_);
lean_inc(v___x_50_);
lean_inc_ref(v_a_45_);
v___x_51_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_45_, v___x_50_);
v___x_52_ = lean_bool_not(v___x_51_);
if (v___x_52_ == 0)
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
return v___x_52_;
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
v___x_70_ = lean_bool_not(v___x_69_);
return v___x_70_;
}
else
{
if (v___x_69_ == 0)
{
uint8_t v___x_71_; 
lean_dec_ref(v_a_65_);
v___x_71_ = lean_bool_not(v___x_69_);
return v___x_71_;
}
else
{
size_t v___x_72_; size_t v___x_73_; uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_72_ = ((size_t)0ULL);
v___x_73_ = lean_usize_of_nat(v___x_68_);
v___x_74_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_65_, v_f_66_, v___x_72_, v___x_73_);
v___x_75_ = lean_bool_not(v___x_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object* v_a_76_, lean_object* v_f_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Std_Sat_CNF_eval___redArg(v_a_76_, v_f_77_);
lean_dec_ref(v_f_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object* v_00_u03b1_80_, lean_object* v_a_81_, lean_object* v_f_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = l_Std_Sat_CNF_eval___redArg(v_a_81_, v_f_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object* v_00_u03b1_84_, lean_object* v_a_85_, lean_object* v_f_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Std_Sat_CNF_eval(v_00_u03b1_84_, v_a_85_, v_f_86_);
lean_dec_ref(v_f_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object* v_00_u03b1_89_, lean_object* v_a_90_, lean_object* v_as_91_, size_t v_i_92_, size_t v_stop_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_90_, v_as_91_, v_i_92_, v_stop_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object* v_00_u03b1_95_, lean_object* v_a_96_, lean_object* v_as_97_, lean_object* v_i_98_, lean_object* v_stop_99_){
_start:
{
size_t v_i_boxed_100_; size_t v_stop_boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_i_boxed_100_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_stop_boxed_101_ = lean_unbox_usize(v_stop_99_);
lean_dec(v_stop_99_);
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(v_00_u03b1_95_, v_a_96_, v_as_97_, v_i_boxed_100_, v_stop_boxed_101_);
lean_dec_ref(v_as_97_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object* v_00_u03b1_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = ((lean_object*)(l_Std_Sat_CNF_empty___closed__0));
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object* v_n_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_mk_empty_array_with_capacity(v_n_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object* v_n_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_110_);
lean_dec(v_n_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object* v_00_u03b1_112_, lean_object* v_n_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_mk_empty_array_with_capacity(v_n_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object* v_00_u03b1_115_, lean_object* v_n_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_115_, v_n_116_);
lean_dec(v_n_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object* v_c_118_, lean_object* v_f_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_array_push(v_f_119_, v_c_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object* v_00_u03b1_121_, lean_object* v_c_122_, lean_object* v_f_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_array_push(v_f_123_, v_c_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object* v_f1_125_, lean_object* v_f2_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Array_append___redArg(v_f1_125_, v_f2_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object* v_f1_128_, lean_object* v_f2_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Sat_CNF_append___redArg(v_f1_128_, v_f2_129_);
lean_dec_ref(v_f2_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object* v_00_u03b1_131_, lean_object* v_f1_132_, lean_object* v_f2_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Array_append___redArg(v_f1_132_, v_f2_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object* v_00_u03b1_135_, lean_object* v_f1_136_, lean_object* v_f2_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Sat_CNF_append(v_00_u03b1_135_, v_f1_136_, v_f2_137_);
lean_dec_ref(v_f2_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object* v_00_u03b1_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___closed__0));
return v___x_141_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_142_; lean_object* v___f_143_; 
v___x_142_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_143_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_143_, 0, v___x_142_);
return v___f_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(lean_object* v_v_144_, lean_object* v_c_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___f_147_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_147_, 0, v_inst_146_);
v___f_148_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0, &l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once, _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0);
v___f_149_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_149_, 0, v___f_147_);
lean_closure_set(v___f_149_, 1, v___f_148_);
v___x_150_ = 0;
v___x_151_ = lean_box(v___x_150_);
lean_inc(v_v_144_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_v_144_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
lean_inc(v_c_145_);
lean_inc_ref(v___f_149_);
v___x_153_ = l_List_elem___redArg(v___f_149_, v___x_152_, v_c_145_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_154_ = 1;
v___x_155_ = lean_box(v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_v_144_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = l_List_elem___redArg(v___f_149_, v___x_156_, v_c_145_);
return v___x_157_;
}
else
{
lean_dec_ref(v___f_149_);
lean_dec(v_c_145_);
lean_dec(v_v_144_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___boxed(lean_object* v_v_158_, lean_object* v_c_159_, lean_object* v_inst_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_158_, v_c_159_, v_inst_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(lean_object* v_00_u03b1_163_, lean_object* v_v_164_, lean_object* v_c_165_, lean_object* v_inst_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_164_, v_c_165_, v_inst_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___boxed(lean_object* v_00_u03b1_168_, lean_object* v_v_169_, lean_object* v_c_170_, lean_object* v_inst_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(v_00_u03b1_168_, v_v_169_, v_c_170_, v_inst_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object* v_v_174_, lean_object* v_c_175_, lean_object* v_inst_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_174_, v_c_175_, v_inst_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* v_v_178_, lean_object* v_c_179_, lean_object* v_inst_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(v_v_178_, v_c_179_, v_inst_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object* v_00_u03b1_183_, lean_object* v_v_184_, lean_object* v_c_185_, lean_object* v_inst_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_184_, v_c_185_, v_inst_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object* v_00_u03b1_188_, lean_object* v_v_189_, lean_object* v_c_190_, lean_object* v_inst_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(v_00_u03b1_188_, v_v_189_, v_c_190_, v_inst_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object* v_00_u03b1_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(lean_object* v_c_196_, lean_object* v_f_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___f_199_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_199_, 0, v_inst_198_);
v___f_200_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0, &l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once, _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0);
v___f_201_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_201_, 0, v___f_199_);
lean_closure_set(v___f_201_, 1, v___f_200_);
v___x_202_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_202_, 0, lean_box(0));
lean_closure_set(v___x_202_, 1, v___f_201_);
v___x_203_ = l_Array_contains___redArg(v___x_202_, v_f_197_, v_c_196_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg___boxed(lean_object* v_c_204_, lean_object* v_f_205_, lean_object* v_inst_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_204_, v_f_205_, v_inst_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(lean_object* v_00_u03b1_209_, lean_object* v_c_210_, lean_object* v_f_211_, lean_object* v_inst_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_210_, v_f_211_, v_inst_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___boxed(lean_object* v_00_u03b1_214_, lean_object* v_c_215_, lean_object* v_f_216_, lean_object* v_inst_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(v_00_u03b1_214_, v_c_215_, v_f_216_, v_inst_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object* v_c_220_, lean_object* v_f_221_, lean_object* v_inst_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_220_, v_f_221_, v_inst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object* v_c_224_, lean_object* v_f_225_, lean_object* v_inst_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_224_, v_f_225_, v_inst_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object* v_00_u03b1_229_, lean_object* v_c_230_, lean_object* v_f_231_, lean_object* v_inst_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(v_c_230_, v_f_231_, v_inst_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object* v_00_u03b1_234_, lean_object* v_c_235_, lean_object* v_f_236_, lean_object* v_inst_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(v_00_u03b1_234_, v_c_235_, v_f_236_, v_inst_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(lean_object* v_v_240_, lean_object* v_inst_241_, lean_object* v_a_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(v_v_240_, v_a_242_, v_inst_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed(lean_object* v_v_244_, lean_object* v_inst_245_, lean_object* v_a_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(v_v_244_, v_inst_245_, v_a_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(lean_object* v_v_249_, lean_object* v_f_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___f_252_; uint8_t v___x_253_; 
v___f_252_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_252_, 0, v_v_249_);
lean_closure_set(v___f_252_, 1, v_inst_251_);
v___x_253_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_f_250_, v___f_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___boxed(lean_object* v_v_254_, lean_object* v_f_255_, lean_object* v_inst_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_254_, v_f_255_, v_inst_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(lean_object* v_00_u03b1_259_, lean_object* v_v_260_, lean_object* v_f_261_, lean_object* v_inst_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_260_, v_f_261_, v_inst_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___boxed(lean_object* v_00_u03b1_264_, lean_object* v_v_265_, lean_object* v_f_266_, lean_object* v_inst_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(v_00_u03b1_264_, v_v_265_, v_f_266_, v_inst_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_270_, lean_object* v_f_271_, lean_object* v_inst_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_270_, v_f_271_, v_inst_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_274_, lean_object* v_f_275_, lean_object* v_inst_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_274_, v_f_275_, v_inst_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_279_, lean_object* v_v_280_, lean_object* v_f_281_, lean_object* v_inst_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(v_v_280_, v_f_281_, v_inst_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_284_, lean_object* v_v_285_, lean_object* v_f_286_, lean_object* v_inst_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(v_00_u03b1_284_, v_v_285_, v_f_286_, v_inst_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(lean_object* v_x_290_){
_start:
{
uint8_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = l_List_isEmpty___redArg(v_x_290_);
v___x_292_ = lean_bool_not(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v_x_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v_x_293_);
lean_dec(v_x_293_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object* v_f_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_array_get_size(v_f_316_);
v___x_319_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9));
v___x_320_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_f_316_);
return v___x_320_;
}
else
{
if (v___x_320_ == 0)
{
lean_dec_ref(v_f_316_);
return v___x_320_;
}
else
{
lean_object* v___f_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___f_321_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__10));
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_318_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_319_, v___f_321_, v_f_316_, v___x_322_, v___x_323_);
v___x_325_ = lean_unbox(v___x_324_);
lean_dec(v___x_324_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object* v_f_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_326_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object* v_00_u03b1_329_, lean_object* v_f_330_, lean_object* v_inst_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_333_, lean_object* v_f_334_, lean_object* v_inst_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(v_00_u03b1_333_, v_f_334_, v_inst_335_);
lean_dec_ref(v_inst_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
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
