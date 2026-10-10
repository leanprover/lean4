// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProofUtil
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value)} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v_snd_2_; 
v_snd_2_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_2_);
return v_snd_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object* v_varPrefix_5_, lean_object* v_toExpr_6_, lean_object* v_varType_7_, uint8_t v___x_8_, lean_object* v_a_9_, lean_object* v_x_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_fst_12_; lean_object* v_fst_13_; lean_object* v_snd_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_27_; 
v_fst_12_ = lean_ctor_get(v_a_9_, 0);
lean_inc(v_fst_12_);
lean_dec_ref(v_a_9_);
v_fst_13_ = lean_ctor_get(v___y_11_, 0);
v_snd_14_ = lean_ctor_get(v___y_11_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v___y_11_);
if (v_isSharedCheck_27_ == 0)
{
v___x_16_ = v___y_11_;
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_snd_14_);
lean_inc(v_fst_13_);
lean_dec(v___y_11_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
lean_inc(v_snd_14_);
v___x_18_ = lean_name_append_index_after(v_varPrefix_5_, v_snd_14_);
v___x_19_ = lean_apply_1(v_toExpr_6_, v_fst_12_);
v___x_20_ = l_Lean_Expr_letE___override(v___x_18_, v_varType_7_, v___x_19_, v_fst_13_, v___x_8_);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_sub(v_snd_14_, v___x_21_);
lean_dec(v_snd_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 1, v___x_22_);
lean_ctor_set(v___x_16_, 0, v___x_20_);
v___x_24_ = v___x_16_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_22_);
v___x_24_ = v_reuseFailAlloc_26_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_varPrefix_5_ = stack[0].m_obj;
lean_object* v_toExpr_6_ = stack[1].m_obj;
lean_object* v_varType_7_ = stack[2].m_obj;
uint8_t v___x_8_ = stack[3].m_num;
lean_object* v_a_9_ = stack[4].m_obj;
lean_object* v___y_11_ = stack[6].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(v_varPrefix_5_, v_toExpr_6_, v_varType_7_, v___x_8_, v_a_9_, lean_box(0), v___y_11_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object* v_varPrefix_29_, lean_object* v_toExpr_30_, lean_object* v_varType_31_, lean_object* v___x_32_, lean_object* v_a_33_, lean_object* v_x_34_, lean_object* v___y_35_){
_start:
{
uint8_t v___x_375__boxed_36_; lean_object* v_res_37_; 
v___x_375__boxed_36_ = lean_unbox(v___x_32_);
v_res_37_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(v_varPrefix_29_, v_toExpr_30_, v_varType_31_, v___x_375__boxed_36_, v_a_33_, v_x_34_, v___y_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object* v_x1_38_, lean_object* v_x2_39_, lean_object* v_x3_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v_x2_39_);
lean_ctor_set(v___x_41_, 1, v_x3_40_);
v___x_42_ = lean_array_push(v_x1_38_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(lean_object* v___x_43_, lean_object* v___f_44_, lean_object* v_acc_45_, lean_object* v_l_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_43_, v___f_44_, v_acc_45_, v_l_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object* v_m_72_, lean_object* v_e_73_, lean_object* v_varPrefix_74_, lean_object* v_varType_75_, lean_object* v_toExpr_76_){
_start:
{
lean_object* v___x_77_; lean_object* v_size_78_; lean_object* v_buckets_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_109_; 
v___x_77_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9));
v_size_78_ = lean_ctor_get(v_m_72_, 0);
v_buckets_79_ = lean_ctor_get(v_m_72_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_m_72_);
if (v_isSharedCheck_109_ == 0)
{
v___x_81_ = v_m_72_;
v_isShared_82_ = v_isSharedCheck_109_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_buckets_79_);
lean_inc(v_size_78_);
lean_dec(v_m_72_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_109_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_nat_dec_eq(v_size_78_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___y_89_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___f_85_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10));
v___x_86_ = lean_box(v___x_84_);
v___f_87_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_87_, 0, v_varPrefix_74_);
lean_closure_set(v___f_87_, 1, v_toExpr_76_);
lean_closure_set(v___f_87_, 2, v_varType_75_);
lean_closure_set(v___f_87_, 3, v___x_86_);
v___x_102_ = lean_mk_empty_array_with_capacity(v_size_78_);
lean_dec(v_size_78_);
v___x_103_ = lean_array_get_size(v_buckets_79_);
v___x_104_ = lean_nat_dec_lt(v___x_83_, v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_buckets_79_);
v___y_89_ = v___x_102_;
goto v___jp_88_;
}
else
{
lean_object* v___f_105_; size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; 
v___f_105_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12));
v___x_106_ = ((size_t)0ULL);
v___x_107_ = lean_usize_of_nat(v___x_103_);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_77_, v___f_105_, v_buckets_79_, v___x_106_, v___x_107_, v___x_102_);
v___y_89_ = v___x_108_;
goto v___jp_88_;
}
v___jp_88_:
{
size_t v_sz_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v_e_93_; lean_object* v_i_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v_sz_90_ = lean_array_size(v___y_89_);
v___x_91_ = ((size_t)0ULL);
lean_inc_ref(v___y_89_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_77_, v___f_85_, v_sz_90_, v___x_91_, v___y_89_);
v_e_93_ = lean_expr_abstract(v_e_73_, v___x_92_);
lean_dec(v___x_92_);
v_i_94_ = lean_array_get_size(v___y_89_);
v___x_95_ = l_Array_reverse___redArg(v___y_89_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_i_94_);
lean_ctor_set(v___x_81_, 0, v_e_93_);
v___x_97_ = v___x_81_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_e_93_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_i_94_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
size_t v_sz_98_; lean_object* v___x_99_; lean_object* v_fst_100_; 
v_sz_98_ = lean_array_size(v___x_95_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_77_, v___x_95_, v___f_87_, v_sz_98_, v___x_91_, v___x_97_);
v_fst_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_fst_100_);
lean_dec(v___x_99_);
return v_fst_100_;
}
}
}
else
{
lean_del_object(v___x_81_);
lean_dec_ref(v_buckets_79_);
lean_dec(v_size_78_);
lean_dec_ref(v_toExpr_76_);
lean_dec_ref(v_varType_75_);
lean_dec(v_varPrefix_74_);
lean_inc_ref(v_e_73_);
return v_e_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object* v_m_110_, lean_object* v_e_111_, lean_object* v_varPrefix_112_, lean_object* v_varType_113_, lean_object* v_toExpr_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(v_m_110_, v_e_111_, v_varPrefix_112_, v_varType_113_, v_toExpr_114_);
lean_dec_ref(v_e_111_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object* v_00_u03b1_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_m_119_, lean_object* v_e_120_, lean_object* v_varPrefix_121_, lean_object* v_varType_122_, lean_object* v_toExpr_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(v_m_119_, v_e_120_, v_varPrefix_121_, v_varType_122_, v_toExpr_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object* v_00_u03b1_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_m_128_, lean_object* v_e_129_, lean_object* v_varPrefix_130_, lean_object* v_varType_131_, lean_object* v_toExpr_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_Grind_mkLetOfMap(v_00_u03b1_125_, v_x_126_, v_x_127_, v_m_128_, v_e_129_, v_varPrefix_130_, v_varType_131_, v_toExpr_132_);
lean_dec_ref(v_e_129_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
return v_res_133_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
}
#ifdef __cplusplus
}
#endif
