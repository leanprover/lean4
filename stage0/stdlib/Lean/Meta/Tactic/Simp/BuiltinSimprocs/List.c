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
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceReplicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_reduceReplicate___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(0, 105, 104, 187, 83, 144, 177, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_reduceReplicate___redArg___closed__3_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_reduceReplicate___redArg(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_8_, v_a_10_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_80_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_80_ == 0)
{
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_80_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_80_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l_Lean_Expr_cleanupAnnotations(v_a_15_);
v___x_25_ = l_Lean_Expr_isApp(v___x_24_);
if (v___x_25_ == 0)
{
lean_dec_ref(v___x_24_);
goto v___jp_19_;
}
else
{
lean_object* v_arg_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_arg_26_ = lean_ctor_get(v___x_24_, 1);
lean_inc_ref(v_arg_26_);
v___x_27_ = l_Lean_Expr_appFnCleanup___redArg(v___x_24_);
v___x_28_ = l_Lean_Expr_isApp(v___x_27_);
if (v___x_28_ == 0)
{
lean_dec_ref(v___x_27_);
lean_dec_ref(v_arg_26_);
goto v___jp_19_;
}
else
{
lean_object* v_arg_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_arg_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc_ref(v_arg_29_);
v___x_30_ = l_Lean_Expr_appFnCleanup___redArg(v___x_27_);
v___x_31_ = l_Lean_Expr_isApp(v___x_30_);
if (v___x_31_ == 0)
{
lean_dec_ref(v___x_30_);
lean_dec_ref(v_arg_29_);
lean_dec_ref(v_arg_26_);
goto v___jp_19_;
}
else
{
lean_object* v_arg_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_arg_32_ = lean_ctor_get(v___x_30_, 1);
lean_inc_ref(v_arg_32_);
v___x_33_ = l_Lean_Expr_appFnCleanup___redArg(v___x_30_);
v___x_34_ = ((lean_object*)(l_List_reduceReplicate___redArg___closed__3));
v___x_35_ = l_Lean_Expr_isConstOf(v___x_33_, v___x_34_);
lean_dec_ref(v___x_33_);
if (v___x_35_ == 0)
{
lean_dec_ref(v_arg_32_);
lean_dec_ref(v_arg_29_);
lean_dec_ref(v_arg_26_);
goto v___jp_19_;
}
else
{
lean_object* v___x_36_; 
lean_del_object(v___x_17_);
v___x_36_ = l_Lean_Meta_getNatValue_x3f(v_arg_29_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_arg_29_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_71_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_71_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_71_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_71_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
if (lean_obj_tag(v_a_37_) == 1)
{
lean_object* v_val_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_66_; 
lean_del_object(v___x_39_);
v_val_41_ = lean_ctor_get(v_a_37_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v_a_37_);
if (v_isSharedCheck_66_ == 0)
{
v___x_43_ = v_a_37_;
v_isShared_44_ = v_isSharedCheck_66_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_val_41_);
lean_dec(v_a_37_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_66_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = l_List_replicateTR___redArg(v_val_41_, v_arg_26_);
v___x_46_ = l_Lean_Meta_mkListLit(v_arg_32_, v___x_45_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_57_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_57_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_57_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_57_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set_tag(v___x_43_, 0);
lean_ctor_set(v___x_43_, 0, v_a_47_);
v___x_52_ = v___x_43_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
lean_del_object(v___x_43_);
v_a_58_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_46_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_46_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
else
{
lean_object* v___x_67_; lean_object* v___x_69_; 
lean_dec(v_a_37_);
lean_dec_ref(v_arg_32_);
lean_dec_ref(v_arg_26_);
v___x_67_ = ((lean_object*)(l_List_reduceReplicate___redArg___closed__0));
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_67_);
v___x_69_ = v___x_39_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec_ref(v_arg_32_);
lean_dec_ref(v_arg_26_);
v_a_72_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_36_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_36_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
}
v___jp_19_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = ((lean_object*)(l_List_reduceReplicate___redArg___closed__0));
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_20_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_a_81_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_14_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_14_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reduceReplicate___redArg___boxed(lean_object* v_e_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_List_reduceReplicate___redArg(v_e_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_List_reduceReplicate(lean_object* v_e_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_List_reduceReplicate___redArg(v_e_96_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_List_reduceReplicate___boxed(lean_object* v_e_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_List_reduceReplicate(v_e_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_));
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_));
v___x_134_ = lean_alloc_closure((void*)(l_List_reduceReplicate___boxed), 9, 0);
v___x_135_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_132_, v___x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14____boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_();
return v_res_137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_alloc_closure((void*)(l_List_reduceReplicate___boxed), 9, 0);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_));
v___x_142_ = 1;
v___x_143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_);
v___x_144_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_141_, v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_));
v___x_149_ = 1;
v___x_150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_);
v___x_151_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_148_, v___x_149_, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18____boxed(lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_();
return v_res_153_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_();
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
