// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.List
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
static const lean_ctor_object l_List_reduceReplicate___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_reduceReplicate___redArg___closed__0 = (const lean_object*)&l_List_reduceReplicate___redArg___closed__0_value;
static const lean_string_object l_List_reduceReplicate___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_List_reduceReplicate___redArg___closed__1 = (const lean_object*)&l_List_reduceReplicate___redArg___closed__1_value;
static const lean_string_object l_List_reduceReplicate___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_List_reduceReplicate___redArg___closed__2 = (const lean_object*)&l_List_reduceReplicate___redArg___closed__2_value;
static const lean_ctor_object l_List_reduceReplicate___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_reduceReplicate___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_reduceReplicate___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_reduceReplicate___redArg___closed__3_value_aux_0),((lean_object*)&l_List_reduceReplicate___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 254, 27, 73, 83, 86, 207, 8)}};
static const lean_object* l_List_reduceReplicate___redArg___closed__3 = (const lean_object*)&l_List_reduceReplicate___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_reduceReplicate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reduceReplicate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reduceReplicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reduceReplicate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceReplicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_reduceReplicate___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(0, 105, 104, 187, 83, 144, 177, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_reduceReplicate___redArg___closed__3_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_reduceReplicate___redArg(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_8_, v_a_10_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
lean_dec_ref_known(v___x_17_, 1);
v___x_19_ = l_Lean_Expr_cleanupAnnotations(v_a_18_);
v___x_20_ = l_Lean_Expr_isApp(v___x_19_);
if (v___x_20_ == 0)
{
lean_dec_ref(v___x_19_);
goto v___jp_14_;
}
else
{
lean_object* v_arg_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_arg_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc_ref(v_arg_21_);
v___x_22_ = l_Lean_Expr_appFnCleanup___redArg(v___x_19_);
v___x_23_ = l_Lean_Expr_isApp(v___x_22_);
if (v___x_23_ == 0)
{
lean_dec_ref(v___x_22_);
lean_dec_ref(v_arg_21_);
goto v___jp_14_;
}
else
{
lean_object* v_arg_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_arg_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc_ref(v_arg_24_);
v___x_25_ = l_Lean_Expr_appFnCleanup___redArg(v___x_22_);
v___x_26_ = l_Lean_Expr_isApp(v___x_25_);
if (v___x_26_ == 0)
{
lean_dec_ref(v___x_25_);
lean_dec_ref(v_arg_24_);
lean_dec_ref(v_arg_21_);
goto v___jp_14_;
}
else
{
lean_object* v_arg_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_arg_27_ = lean_ctor_get(v___x_25_, 1);
lean_inc_ref(v_arg_27_);
v___x_28_ = l_Lean_Expr_appFnCleanup___redArg(v___x_25_);
v___x_29_ = ((lean_object*)(l_List_reduceReplicate___redArg___closed__3));
v___x_30_ = l_Lean_Expr_isConstOf(v___x_28_, v___x_29_);
lean_dec_ref(v___x_28_);
if (v___x_30_ == 0)
{
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
lean_dec_ref(v_arg_21_);
goto v___jp_14_;
}
else
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_getNatValue_x3f(v_arg_24_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_arg_24_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_66_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_66_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_66_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_66_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
if (lean_obj_tag(v_a_32_) == 1)
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_61_; 
lean_del_object(v___x_34_);
v_val_36_ = lean_ctor_get(v_a_32_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_a_32_);
if (v_isSharedCheck_61_ == 0)
{
v___x_38_ = v_a_32_;
v_isShared_39_ = v_isSharedCheck_61_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v_a_32_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_61_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_List_replicateTR___redArg(v_val_36_, v_arg_21_);
v___x_41_ = l_Lean_Meta_mkListLit(v_arg_27_, v___x_40_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_52_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_52_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_52_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_52_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 0);
lean_ctor_set(v___x_38_, 0, v_a_42_);
v___x_47_ = v___x_38_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_51_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_49_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_47_);
v___x_49_ = v___x_44_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
else
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_del_object(v___x_38_);
v_a_53_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_41_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_41_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
else
{
lean_object* v___x_62_; lean_object* v___x_64_; 
lean_dec(v_a_32_);
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_21_);
v___x_62_ = ((lean_object*)(l_List_reduceReplicate___redArg___closed__0));
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_62_);
v___x_64_ = v___x_34_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_21_);
v_a_67_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_31_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_31_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_17_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_17_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
v___jp_14_:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = ((lean_object*)(l_List_reduceReplicate___redArg___closed__0));
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_List_reduceReplicate___redArg___boxed(lean_object* v_e_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_List_reduceReplicate___redArg(v_e_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_List_reduceReplicate(lean_object* v_e_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_List_reduceReplicate___redArg(v_e_90_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_List_reduceReplicate___boxed(lean_object* v_e_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_List_reduceReplicate(v_e_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_));
v___x_127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_));
v___x_128_ = lean_alloc_closure((void*)(l_List_reduceReplicate___boxed), 9, 0);
v___x_129_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_126_, v___x_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21____boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_();
return v_res_131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_alloc_closure((void*)(l_List_reduceReplicate___boxed), 9, 0);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_));
v___x_136_ = 1;
v___x_137_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_);
v___x_138_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_));
v___x_143_ = 1;
v___x_144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_);
v___x_145_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_142_, v___x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_25____boxed(lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_25_();
return v_res_147_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_4079200032____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
}
#ifdef __cplusplus
}
#endif
