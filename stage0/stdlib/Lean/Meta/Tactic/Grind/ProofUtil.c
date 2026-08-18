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
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value),((lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_, lean_object* v_x3_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_x2_2_);
lean_ctor_set(v___x_4_, 1, v_x3_3_);
v___x_5_ = lean_array_push(v_x1_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object* v_x_6_){
_start:
{
lean_object* v_snd_7_; 
v_snd_7_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_snd_7_);
return v_snd_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object* v_varPrefix_10_, lean_object* v_toExpr_11_, lean_object* v_varType_12_, uint8_t v___x_13_, lean_object* v_a_14_, lean_object* v_x_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_fst_17_; lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_32_; 
v_fst_17_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_fst_17_);
lean_dec_ref(v_a_14_);
v_fst_18_ = lean_ctor_get(v___y_16_, 0);
v_snd_19_ = lean_ctor_get(v___y_16_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v___y_16_);
if (v_isSharedCheck_32_ == 0)
{
v___x_21_ = v___y_16_;
v_isShared_22_ = v_isSharedCheck_32_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snd_19_);
lean_inc(v_fst_18_);
lean_dec(v___y_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_32_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
lean_inc(v_snd_19_);
v___x_23_ = lean_name_append_index_after(v_varPrefix_10_, v_snd_19_);
v___x_24_ = lean_apply_1(v_toExpr_11_, v_fst_17_);
v___x_25_ = l_Lean_Expr_letE___override(v___x_23_, v_varType_12_, v___x_24_, v_fst_18_, v___x_13_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_sub(v_snd_19_, v___x_26_);
lean_dec(v_snd_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v___x_27_);
lean_ctor_set(v___x_21_, 0, v___x_25_);
v___x_29_ = v___x_21_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_27_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2___boxed(lean_object* v_varPrefix_33_, lean_object* v_toExpr_34_, lean_object* v_varType_35_, lean_object* v___x_36_, lean_object* v_a_37_, lean_object* v_x_38_, lean_object* v___y_39_){
_start:
{
uint8_t v___x_448__boxed_40_; lean_object* v_res_41_; 
v___x_448__boxed_40_ = lean_unbox(v___x_36_);
v_res_41_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(v_varPrefix_33_, v_toExpr_34_, v_varType_35_, v___x_448__boxed_40_, v_a_37_, v_x_38_, v___y_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object* v_m_63_, lean_object* v_e_64_, lean_object* v_varPrefix_65_, lean_object* v_varType_66_, lean_object* v_toExpr_67_){
_start:
{
lean_object* v_size_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_size_68_ = lean_ctor_get(v_m_63_, 0);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_eq(v_size_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_as_77_; size_t v_sz_78_; size_t v___x_79_; lean_object* v___x_80_; lean_object* v_e_81_; lean_object* v_i_82_; lean_object* v___x_83_; lean_object* v___x_84_; size_t v_sz_85_; lean_object* v___x_86_; lean_object* v_fst_87_; 
v___f_71_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0));
v___f_72_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1));
v___x_73_ = lean_box(v___x_70_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_74_, 0, v_varPrefix_65_);
lean_closure_set(v___f_74_, 1, v_toExpr_67_);
lean_closure_set(v___f_74_, 2, v_varType_66_);
lean_closure_set(v___f_74_, 3, v___x_73_);
v___x_75_ = lean_mk_empty_array_with_capacity(v_size_68_);
v___x_76_ = ((lean_object*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11));
v_as_77_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_76_, v___f_71_, v___x_75_, v_m_63_);
v_sz_78_ = lean_array_size(v_as_77_);
v___x_79_ = ((size_t)0ULL);
lean_inc(v_as_77_);
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_76_, v___f_72_, v_sz_78_, v___x_79_, v_as_77_);
v_e_81_ = lean_expr_abstract(v_e_64_, v___x_80_);
lean_dec(v___x_80_);
v_i_82_ = lean_array_get_size(v_as_77_);
v___x_83_ = l_Array_reverse___redArg(v_as_77_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v_e_81_);
lean_ctor_set(v___x_84_, 1, v_i_82_);
v_sz_85_ = lean_array_size(v___x_83_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_76_, v___x_83_, v___f_74_, v_sz_85_, v___x_79_, v___x_84_);
v_fst_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_fst_87_);
lean_dec(v___x_86_);
return v_fst_87_;
}
else
{
lean_dec_ref(v_toExpr_67_);
lean_dec_ref(v_varType_66_);
lean_dec(v_varPrefix_65_);
lean_dec_ref(v_m_63_);
lean_inc_ref(v_e_64_);
return v_e_64_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object* v_m_88_, lean_object* v_e_89_, lean_object* v_varPrefix_90_, lean_object* v_varType_91_, lean_object* v_toExpr_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(v_m_88_, v_e_89_, v_varPrefix_90_, v_varType_91_, v_toExpr_92_);
lean_dec_ref(v_e_89_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object* v_00_u03b1_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_m_97_, lean_object* v_e_98_, lean_object* v_varPrefix_99_, lean_object* v_varType_100_, lean_object* v_toExpr_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(v_m_97_, v_e_98_, v_varPrefix_99_, v_varType_100_, v_toExpr_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object* v_00_u03b1_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_m_106_, lean_object* v_e_107_, lean_object* v_varPrefix_108_, lean_object* v_varType_109_, lean_object* v_toExpr_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Meta_Grind_mkLetOfMap(v_00_u03b1_103_, v_x_104_, v_x_105_, v_m_106_, v_e_107_, v_varPrefix_108_, v_varType_109_, v_toExpr_110_);
lean_dec_ref(v_e_107_);
lean_dec_ref(v_x_105_);
lean_dec_ref(v_x_104_);
return v_res_111_;
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
