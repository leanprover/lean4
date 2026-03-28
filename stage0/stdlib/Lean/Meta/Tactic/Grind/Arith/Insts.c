// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Insts
// Imports: public import Lean.Meta.Tactic.Grind.Arith.EvalNum public import Lean.Meta.Tactic.Grind.SynthInstance import Init.Grind.Ring
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsCharP"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 211, 245, 119, 67, 24, 212, 73)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_30_, v___y_38_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object* v_e_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(v_e_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec(v___y_44_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object* v_k_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc(v___y_57_);
v___x_68_ = lean_apply_11(v_k_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, lean_box(0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec(v___y_70_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object* v_k_82_, uint8_t v_allowLevelAssignments_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___f_95_; lean_object* v___x_96_; 
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc(v___y_84_);
v___f_95_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_95_, 0, v_k_82_);
lean_closure_set(v___f_95_, 1, v___y_84_);
lean_closure_set(v___f_95_, 2, v___y_85_);
lean_closure_set(v___f_95_, 3, v___y_86_);
lean_closure_set(v___f_95_, 4, v___y_87_);
lean_closure_set(v___f_95_, 5, v___y_88_);
lean_closure_set(v___f_95_, 6, v___y_89_);
v___x_96_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_83_, v___f_95_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object* v_k_105_, lean_object* v_allowLevelAssignments_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_118_; lean_object* v_res_119_; 
v_allowLevelAssignments_boxed_118_ = lean_unbox(v_allowLevelAssignments_106_);
v_res_119_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_105_, v_allowLevelAssignments_boxed_118_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec(v___y_107_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(lean_object* v_00_u03b1_120_, lean_object* v_k_121_, uint8_t v_allowLevelAssignments_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_121_, v_allowLevelAssignments_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object* v_00_u03b1_135_, lean_object* v_k_136_, lean_object* v_allowLevelAssignments_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_149_; lean_object* v_res_150_; 
v_allowLevelAssignments_boxed_149_ = lean_unbox(v_allowLevelAssignments_137_);
v_res_150_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_135_, v_k_136_, v_allowLevelAssignments_boxed_149_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec(v___y_138_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(lean_object* v___x_158_, uint8_t v___x_159_, lean_object* v___x_160_, lean_object* v_u_161_, lean_object* v___x_162_, lean_object* v_type_163_, lean_object* v_semiringInst_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_mkFreshExprMVar(v___x_158_, v___x_159_, v___x_160_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_charType_181_; lean_object* v___x_182_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_n(v_a_177_, 2);
lean_dec_ref(v___x_176_);
v___x_178_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3));
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v_u_161_);
lean_ctor_set(v___x_179_, 1, v___x_162_);
v___x_180_ = l_Lean_mkConst(v___x_178_, v___x_179_);
v_charType_181_ = l_Lean_mkApp3(v___x_180_, v_type_163_, v_semiringInst_164_, v_a_177_);
v___x_182_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_charType_181_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_224_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_224_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_224_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_224_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
if (lean_obj_tag(v_a_183_) == 1)
{
lean_object* v_val_187_; lean_object* v___x_188_; lean_object* v_a_189_; lean_object* v___x_190_; 
lean_del_object(v___x_185_);
v_val_187_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v_a_183_);
v___x_188_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_177_, v___y_172_);
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v___x_188_);
v___x_190_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(v_a_189_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_211_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_211_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
if (lean_obj_tag(v_a_191_) == 1)
{
lean_object* v_val_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_206_; 
v_val_195_ = lean_ctor_get(v_a_191_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_a_191_);
if (v_isSharedCheck_206_ == 0)
{
v___x_197_ = v_a_191_;
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_val_195_);
lean_dec(v_a_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_val_187_);
lean_ctor_set(v___x_199_, 1, v_val_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_201_);
v___x_203_ = v___x_193_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec(v_a_191_);
lean_dec(v_val_187_);
v___x_207_ = lean_box(0);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_207_);
v___x_209_ = v___x_193_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_val_187_);
v_a_212_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_190_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_190_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec(v_a_183_);
lean_dec(v_a_177_);
v___x_220_ = lean_box(0);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_220_);
v___x_222_ = v___x_185_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_a_177_);
v_a_225_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_182_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_182_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_semiringInst_164_);
lean_dec_ref(v_type_163_);
lean_dec(v___x_162_);
lean_dec(v_u_161_);
v_a_233_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_176_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_176_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_241_ = _args[0];
lean_object* v___x_242_ = _args[1];
lean_object* v___x_243_ = _args[2];
lean_object* v_u_244_ = _args[3];
lean_object* v___x_245_ = _args[4];
lean_object* v_type_246_ = _args[5];
lean_object* v_semiringInst_247_ = _args[6];
lean_object* v___y_248_ = _args[7];
lean_object* v___y_249_ = _args[8];
lean_object* v___y_250_ = _args[9];
lean_object* v___y_251_ = _args[10];
lean_object* v___y_252_ = _args[11];
lean_object* v___y_253_ = _args[12];
lean_object* v___y_254_ = _args[13];
lean_object* v___y_255_ = _args[14];
lean_object* v___y_256_ = _args[15];
lean_object* v___y_257_ = _args[16];
lean_object* v___y_258_ = _args[17];
_start:
{
uint8_t v___x_9036__boxed_259_; lean_object* v_res_260_; 
v___x_9036__boxed_259_ = lean_unbox(v___x_242_);
v_res_260_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(v___x_241_, v___x_9036__boxed_259_, v___x_243_, v_u_244_, v___x_245_, v_type_246_, v_semiringInst_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec(v___y_248_);
return v_res_260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1));
v___x_266_ = l_Lean_mkConst(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2, &l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object* v_u_269_, lean_object* v_type_270_, lean_object* v_semiringInst_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___f_288_; uint8_t v___x_289_; lean_object* v___x_290_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3, &l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once, _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3);
v___x_285_ = 0;
v___x_286_ = lean_box(0);
v___x_287_ = lean_box(v___x_285_);
v___f_288_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed), 18, 7);
lean_closure_set(v___f_288_, 0, v___x_284_);
lean_closure_set(v___f_288_, 1, v___x_287_);
lean_closure_set(v___f_288_, 2, v___x_286_);
lean_closure_set(v___f_288_, 3, v_u_269_);
lean_closure_set(v___f_288_, 4, v___x_283_);
lean_closure_set(v___f_288_, 5, v_type_270_);
lean_closure_set(v___f_288_, 6, v_semiringInst_271_);
v___x_289_ = 0;
v___x_290_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_288_, v___x_289_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___boxed(lean_object* v_u_291_, lean_object* v_type_292_, lean_object* v_semiringInst_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_u_291_, v_type_292_, v_semiringInst_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec(v_a_294_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object* v_u_316_, lean_object* v_type_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_natModuleType_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1));
v___x_324_ = lean_box(0);
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v_u_316_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
lean_inc_ref(v___x_325_);
v___x_326_ = l_Lean_mkConst(v___x_323_, v___x_325_);
lean_inc_ref(v_type_317_);
v_natModuleType_327_ = l_Lean_Expr_app___override(v___x_326_, v_type_317_);
v___x_328_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_natModuleType_327_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_342_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_342_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_342_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_342_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
if (lean_obj_tag(v_a_329_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_del_object(v___x_331_);
v_val_333_ = lean_ctor_get(v_a_329_, 0);
lean_inc(v_val_333_);
lean_dec_ref(v_a_329_);
v___x_334_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3));
v___x_335_ = l_Lean_mkConst(v___x_334_, v___x_325_);
v___x_336_ = l_Lean_mkAppB(v___x_335_, v_type_317_, v_val_333_);
v___x_337_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_336_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_340_; 
lean_dec(v_a_329_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v_type_317_);
v___x_338_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_338_);
v___x_340_ = v___x_331_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_dec_ref(v___x_325_);
lean_dec_ref(v_type_317_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object* v_u_343_, lean_object* v_type_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_u_343_, v_type_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(lean_object* v_u_351_, lean_object* v_type_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_u_351_, v_type_352_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___boxed(lean_object* v_u_365_, lean_object* v_type_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(v_u_365_, v_type_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec(v_a_367_);
return v_res_378_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
}
#ifdef __cplusplus
}
#endif
