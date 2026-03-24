// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.CtorIdx
// Imports: public import Lean.Meta.Tactic.Simp.Simproc import Init.Simproc import Lean.Meta.Constructions.CtorIdx import Lean.Meta.CtorRecognizer
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_reduceCtorIdx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceCtorIdx___closed__0;
LEAN_EXPORT lean_object* l_reduceCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceCtorIdx"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(47, 140, 108, 243, 19, 200, 28, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
if (lean_obj_tag(v_x_3_) == 5)
{
lean_object* v_fn_11_; lean_object* v_arg_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_fn_11_ = lean_ctor_get(v_x_3_, 0);
lean_inc_ref(v_fn_11_);
v_arg_12_ = lean_ctor_get(v_x_3_, 1);
lean_inc_ref(v_arg_12_);
lean_dec_ref(v_x_3_);
v___x_13_ = lean_array_set(v_x_4_, v_x_5_, v_arg_12_);
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_sub(v_x_5_, v___x_14_);
lean_dec(v_x_5_);
v_x_3_ = v_fn_11_;
v_x_4_ = v___x_13_;
v_x_5_ = v___x_15_;
goto _start;
}
else
{
lean_object* v___x_17_; 
lean_dec(v_x_5_);
v___x_17_ = l_Lean_Expr_constName_x3f(v_x_3_);
lean_dec_ref(v_x_3_);
if (lean_obj_tag(v___x_17_) == 1)
{
lean_object* v_val_18_; lean_object* v___x_19_; 
v_val_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_val_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = l_isCtorIdx_x3f___redArg(v_val_18_, v___y_9_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_74_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_74_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_74_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_74_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
if (lean_obj_tag(v_a_20_) == 1)
{
lean_object* v_val_24_; lean_object* v_numParams_25_; lean_object* v_numIndices_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_val_24_ = lean_ctor_get(v_a_20_, 0);
lean_inc(v_val_24_);
lean_dec_ref(v_a_20_);
v_numParams_25_ = lean_ctor_get(v_val_24_, 1);
lean_inc(v_numParams_25_);
v_numIndices_26_ = lean_ctor_get(v_val_24_, 2);
lean_inc(v_numIndices_26_);
lean_dec(v_val_24_);
v___x_27_ = lean_array_get_size(v_x_4_);
v___x_28_ = lean_nat_add(v_numParams_25_, v_numIndices_26_);
lean_dec(v_numIndices_26_);
lean_dec(v_numParams_25_);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_add(v___x_28_, v___x_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_nat_dec_eq(v___x_27_, v___x_30_);
lean_dec(v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_34_; 
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v_x_4_);
v___x_32_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0));
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_32_);
v___x_34_ = v___x_22_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_del_object(v___x_22_);
v___x_36_ = l_Lean_instInhabitedExpr;
v___x_37_ = lean_nat_sub(v___x_27_, v___x_29_);
v___x_38_ = lean_array_get(v___x_36_, v_x_4_, v___x_37_);
lean_dec(v___x_37_);
lean_dec_ref(v_x_4_);
v___x_39_ = l_Lean_Meta_isConstructorApp_x3f(v___x_38_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_61_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_61_ == 0)
{
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_61_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_61_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
if (lean_obj_tag(v_a_40_) == 1)
{
lean_object* v_val_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_56_; 
v_val_44_ = lean_ctor_get(v_a_40_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v_a_40_);
if (v_isSharedCheck_56_ == 0)
{
v___x_46_ = v_a_40_;
v_isShared_47_ = v_isSharedCheck_56_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_val_44_);
lean_dec(v_a_40_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_56_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_cidx_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v_cidx_48_ = lean_ctor_get(v_val_44_, 2);
lean_inc(v_cidx_48_);
lean_dec(v_val_44_);
v___x_49_ = l_Lean_mkNatLit(v_cidx_48_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 0);
lean_ctor_set(v___x_46_, 0, v___x_49_);
v___x_51_ = v___x_46_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_55_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_53_; 
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_51_);
v___x_53_ = v___x_42_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_59_; 
lean_dec(v_a_40_);
v___x_57_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0));
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_57_);
v___x_59_ = v___x_42_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_39_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_39_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_72_; 
lean_dec(v_a_20_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v_x_4_);
v___x_70_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0));
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_70_);
v___x_72_ = v___x_22_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
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
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v_x_4_);
v_a_75_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_19_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_19_);
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
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v___x_17_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v___y_7_);
lean_dec_ref(v___y_6_);
lean_dec_ref(v_x_4_);
v___x_83_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0));
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___boxed(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(v_x_85_, v_x_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v_res_93_;
}
}
static lean_object* _init_l_reduceCtorIdx___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v_dummy_95_; 
v___x_94_ = lean_box(0);
v_dummy_95_ = l_Lean_Expr_sort___override(v___x_94_);
return v_dummy_95_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorIdx(lean_object* v_e_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_dummy_105_; lean_object* v_nargs_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_dummy_105_ = lean_obj_once(&l_reduceCtorIdx___closed__0, &l_reduceCtorIdx___closed__0_once, _init_l_reduceCtorIdx___closed__0);
v_nargs_106_ = l_Lean_Expr_getAppNumArgs(v_e_96_);
lean_inc(v_nargs_106_);
v___x_107_ = lean_mk_array(v_nargs_106_, v_dummy_105_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_sub(v_nargs_106_, v___x_108_);
lean_dec(v_nargs_106_);
v___x_110_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(v_e_96_, v___x_107_, v___x_109_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorIdx___boxed(lean_object* v_e_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_reduceCtorIdx(v_e_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(v_x_121_, v_x_122_, v_x_123_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___boxed(lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(v_x_133_, v_x_134_, v_x_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_));
v___x_154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_));
v___x_155_ = lean_alloc_closure((void*)(l_reduceCtorIdx___boxed), 9, 0);
v___x_156_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_153_, v___x_154_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9____boxed(lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
return v_res_158_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
