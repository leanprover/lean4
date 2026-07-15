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
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value)} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object* v_varPrefix_5_, lean_object* v_toExpr_6_, lean_object* v_varType_7_, uint8_t v___x_8_, lean_object* v_a_9_, lean_object* v_x_10_, lean_object* v___y_11_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object* v_varPrefix_28_, lean_object* v_toExpr_29_, lean_object* v_varType_30_, lean_object* v___x_31_, lean_object* v_a_32_, lean_object* v_x_33_, lean_object* v___y_34_){
_start:
{
uint8_t v___x_503__boxed_35_; lean_object* v_res_36_; 
v___x_503__boxed_35_ = lean_unbox(v___x_31_);
v_res_36_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(v_varPrefix_28_, v_toExpr_29_, v_varType_30_, v___x_503__boxed_35_, v_a_32_, v_x_33_, v___y_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object* v_x1_37_, lean_object* v_x2_38_, lean_object* v_x3_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v_x2_38_);
lean_ctor_set(v___x_40_, 1, v_x3_39_);
v___x_41_ = lean_array_push(v_x1_37_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(lean_object* v___x_42_, lean_object* v___f_43_, lean_object* v_acc_44_, lean_object* v_l_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_42_, v___f_43_, v_acc_44_, v_l_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object* v_m_71_, lean_object* v_e_72_, lean_object* v_varPrefix_73_, lean_object* v_varType_74_, lean_object* v_toExpr_75_){
_start:
{
lean_object* v_size_76_; lean_object* v_buckets_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_113_; 
v_size_76_ = lean_ctor_get(v_m_71_, 0);
v_buckets_77_ = lean_ctor_get(v_m_71_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_m_71_);
if (v_isSharedCheck_113_ == 0)
{
v___x_79_ = v_m_71_;
v_isShared_80_ = v_isSharedCheck_113_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_buckets_77_);
lean_inc(v_size_76_);
lean_dec(v_m_71_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_113_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v_size_76_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___y_87_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___f_83_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0));
v___x_84_ = lean_box(v___x_82_);
v___f_85_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_85_, 0, v_varPrefix_73_);
lean_closure_set(v___f_85_, 1, v_toExpr_75_);
lean_closure_set(v___f_85_, 2, v_varType_74_);
lean_closure_set(v___f_85_, 3, v___x_84_);
v___x_101_ = lean_mk_empty_array_with_capacity(v_size_76_);
lean_dec(v_size_76_);
v___x_102_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10));
v___x_103_ = lean_array_get_size(v_buckets_77_);
v___x_104_ = lean_nat_dec_lt(v___x_81_, v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_buckets_77_);
v___y_87_ = v___x_101_;
goto v___jp_86_;
}
else
{
lean_object* v___f_105_; uint8_t v___x_106_; 
v___f_105_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12));
v___x_106_ = lean_nat_dec_le(v___x_103_, v___x_103_);
if (v___x_106_ == 0)
{
if (v___x_104_ == 0)
{
lean_dec_ref(v_buckets_77_);
v___y_87_ = v___x_101_;
goto v___jp_86_;
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_103_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_102_, v___f_105_, v_buckets_77_, v___x_107_, v___x_108_, v___x_101_);
v___y_87_ = v___x_109_;
goto v___jp_86_;
}
}
else
{
size_t v___x_110_; size_t v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((size_t)0ULL);
v___x_111_ = lean_usize_of_nat(v___x_103_);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_102_, v___f_105_, v_buckets_77_, v___x_110_, v___x_111_, v___x_101_);
v___y_87_ = v___x_112_;
goto v___jp_86_;
}
}
v___jp_86_:
{
lean_object* v___x_88_; size_t v_sz_89_; size_t v___x_90_; lean_object* v___x_91_; lean_object* v_e_92_; lean_object* v_i_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_88_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10));
v_sz_89_ = lean_array_size(v___y_87_);
v___x_90_ = ((size_t)0ULL);
lean_inc_ref(v___y_87_);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_88_, v___f_83_, v_sz_89_, v___x_90_, v___y_87_);
v_e_92_ = lean_expr_abstract(v_e_72_, v___x_91_);
lean_dec(v___x_91_);
v_i_93_ = lean_array_get_size(v___y_87_);
v___x_94_ = l_Array_reverse___redArg(v___y_87_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v_i_93_);
lean_ctor_set(v___x_79_, 0, v_e_92_);
v___x_96_ = v___x_79_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_e_92_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_i_93_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
size_t v_sz_97_; lean_object* v___x_98_; lean_object* v_fst_99_; 
v_sz_97_ = lean_array_size(v___x_94_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_88_, v___x_94_, v___f_85_, v_sz_97_, v___x_90_, v___x_96_);
v_fst_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_fst_99_);
lean_dec(v___x_98_);
return v_fst_99_;
}
}
}
else
{
lean_del_object(v___x_79_);
lean_dec_ref(v_buckets_77_);
lean_dec(v_size_76_);
lean_dec_ref(v_toExpr_75_);
lean_dec_ref(v_varType_74_);
lean_dec(v_varPrefix_73_);
lean_inc_ref(v_e_72_);
return v_e_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object* v_m_114_, lean_object* v_e_115_, lean_object* v_varPrefix_116_, lean_object* v_varType_117_, lean_object* v_toExpr_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(v_m_114_, v_e_115_, v_varPrefix_116_, v_varType_117_, v_toExpr_118_);
lean_dec_ref(v_e_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object* v_00_u03b1_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_m_123_, lean_object* v_e_124_, lean_object* v_varPrefix_125_, lean_object* v_varType_126_, lean_object* v_toExpr_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(v_m_123_, v_e_124_, v_varPrefix_125_, v_varType_126_, v_toExpr_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object* v_00_u03b1_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_m_132_, lean_object* v_e_133_, lean_object* v_varPrefix_134_, lean_object* v_varType_135_, lean_object* v_toExpr_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Meta_Grind_mkLetOfMap(v_00_u03b1_129_, v_x_130_, v_x_131_, v_m_132_, v_e_133_, v_varPrefix_134_, v_varType_135_, v_toExpr_136_);
lean_dec_ref(v_e_133_);
lean_dec_ref(v_x_131_);
lean_dec_ref(v_x_130_);
return v_res_137_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
