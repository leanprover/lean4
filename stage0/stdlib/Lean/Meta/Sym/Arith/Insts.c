// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Insts
// Imports: public import Lean.Meta.Sym.Arith.EvalNum import Lean.Meta.Sym.SynthInstance import Init.Grind.Ring
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsCharP"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 211, 245, 119, 67, 24, 212, 73)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PowIdentity"};
static const lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_30_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object* v_k_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
v___x_56_ = lean_apply_7(v_k_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, lean_box(0));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object* v_k_66_, uint8_t v_allowLevelAssignments_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___f_75_; lean_object* v___x_76_; 
lean_inc(v___y_69_);
lean_inc_ref(v___y_68_);
v___f_75_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_75_, 0, v_k_66_);
lean_closure_set(v___f_75_, 1, v___y_68_);
lean_closure_set(v___f_75_, 2, v___y_69_);
v___x_76_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_67_, v___f_75_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
if (lean_obj_tag(v___x_76_) == 0)
{
return v___x_76_;
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object* v_k_85_, lean_object* v_allowLevelAssignments_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_94_; lean_object* v_res_95_; 
v_allowLevelAssignments_boxed_94_ = lean_unbox(v_allowLevelAssignments_86_);
v_res_95_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_85_, v_allowLevelAssignments_boxed_94_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(lean_object* v_00_u03b1_96_, lean_object* v_k_97_, uint8_t v_allowLevelAssignments_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_97_, v_allowLevelAssignments_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object* v_00_u03b1_107_, lean_object* v_k_108_, lean_object* v_allowLevelAssignments_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_117_; lean_object* v_res_118_; 
v_allowLevelAssignments_boxed_117_ = lean_unbox(v_allowLevelAssignments_109_);
v_res_118_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_107_, v_k_108_, v_allowLevelAssignments_boxed_117_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(lean_object* v___x_126_, uint8_t v___x_127_, lean_object* v___x_128_, lean_object* v_u_129_, lean_object* v___x_130_, lean_object* v_type_131_, lean_object* v_semiringInst_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_mkFreshExprMVar(v___x_126_, v___x_127_, v___x_128_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_charType_145_; lean_object* v___x_146_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_n(v_a_141_, 2);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3));
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v_u_129_);
lean_ctor_set(v___x_143_, 1, v___x_130_);
v___x_144_ = l_Lean_mkConst(v___x_142_, v___x_143_);
v_charType_145_ = l_Lean_mkApp3(v___x_144_, v_type_131_, v_semiringInst_132_, v_a_141_);
v___x_146_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_charType_145_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_188_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_188_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_188_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_188_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
if (lean_obj_tag(v_a_147_) == 1)
{
lean_object* v_val_151_; lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_154_; 
lean_del_object(v___x_149_);
v_val_151_ = lean_ctor_get(v_a_147_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v_a_147_, 1);
v___x_152_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_141_, v___y_136_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref(v___x_152_);
v___x_154_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_a_153_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_175_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_175_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_175_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_175_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
if (lean_obj_tag(v_a_155_) == 1)
{
lean_object* v_val_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_170_; 
v_val_159_ = lean_ctor_get(v_a_155_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_a_155_);
if (v_isSharedCheck_170_ == 0)
{
v___x_161_ = v_a_155_;
v_isShared_162_ = v_isSharedCheck_170_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_val_159_);
lean_dec(v_a_155_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_170_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_val_151_);
lean_ctor_set(v___x_163_, 1, v_val_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_165_);
v___x_167_ = v___x_157_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_dec(v_a_155_);
lean_dec(v_val_151_);
v___x_171_ = lean_box(0);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_171_);
v___x_173_ = v___x_157_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_val_151_);
v_a_176_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_154_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_154_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v_a_147_);
lean_dec(v_a_141_);
v___x_184_ = lean_box(0);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_184_);
v___x_186_ = v___x_149_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_a_141_);
v_a_189_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_146_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_146_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_semiringInst_132_);
lean_dec_ref(v_type_131_);
lean_dec(v___x_130_);
lean_dec(v_u_129_);
v_a_197_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_140_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_140_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v_u_208_, lean_object* v___x_209_, lean_object* v_type_210_, lean_object* v_semiringInst_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v___x_3864__boxed_219_; lean_object* v_res_220_; 
v___x_3864__boxed_219_ = lean_unbox(v___x_206_);
v_res_220_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(v___x_205_, v___x_3864__boxed_219_, v___x_207_, v_u_208_, v___x_209_, v_type_210_, v_semiringInst_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
v___x_225_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1));
v___x_226_ = l_Lean_mkConst(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2, &l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once, _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object* v_u_229_, lean_object* v_type_230_, lean_object* v_semiringInst_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___f_244_; uint8_t v___x_245_; lean_object* v___x_246_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3, &l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once, _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3);
v___x_241_ = 0;
v___x_242_ = lean_box(0);
v___x_243_ = lean_box(v___x_241_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed), 14, 7);
lean_closure_set(v___f_244_, 0, v___x_240_);
lean_closure_set(v___f_244_, 1, v___x_243_);
lean_closure_set(v___f_244_, 2, v___x_242_);
lean_closure_set(v___f_244_, 3, v_u_229_);
lean_closure_set(v___f_244_, 4, v___x_239_);
lean_closure_set(v___f_244_, 5, v_type_230_);
lean_closure_set(v___f_244_, 6, v_semiringInst_231_);
v___x_245_ = 0;
v___x_246_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_244_, v___x_245_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(lean_object* v_u_247_, lean_object* v_type_248_, lean_object* v_semiringInst_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_u_247_, v_type_248_, v_semiringInst_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0(lean_object* v___x_259_, uint8_t v___x_260_, lean_object* v___x_261_, lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v___x_265_, lean_object* v_type_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
lean_inc(v___x_261_);
v___x_274_ = l_Lean_Meta_mkFreshExprMVar(v___x_259_, v___x_260_, v___x_261_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_274_, 1);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1));
v___x_277_ = l_Lean_mkConst(v___x_276_, v___x_262_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = l_Lean_Meta_mkFreshExprMVar(v___x_278_, v___x_260_, v___x_261_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_n(v_a_280_, 2);
lean_dec_ref_known(v___x_279_, 1);
v___x_281_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___closed__0));
v___x_282_ = l_Lean_Name_mkStr3(v___x_263_, v___x_264_, v___x_281_);
v___x_283_ = l_Lean_mkConst(v___x_282_, v___x_265_);
lean_inc(v_a_275_);
v___x_284_ = l_Lean_mkApp3(v___x_283_, v_type_266_, v_a_275_, v_a_280_);
v___x_285_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_284_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_330_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_330_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_330_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_330_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
if (lean_obj_tag(v_a_286_) == 1)
{
lean_object* v_val_290_; lean_object* v___x_291_; lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v_a_294_; lean_object* v___x_295_; 
lean_del_object(v___x_288_);
v_val_290_ = lean_ctor_get(v_a_286_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v_a_286_, 1);
v___x_291_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_275_, v___y_270_);
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref(v___x_291_);
v___x_293_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_280_, v___y_270_);
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref(v___x_293_);
v___x_295_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_a_294_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_317_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_317_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
if (lean_obj_tag(v_a_296_) == 1)
{
lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_312_; 
v_val_300_ = lean_ctor_get(v_a_296_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_312_ == 0)
{
v___x_302_ = v_a_296_;
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_dec(v_a_296_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_a_292_);
lean_ctor_set(v___x_304_, 1, v_val_300_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_val_290_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_307_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_315_; 
lean_dec(v_a_296_);
lean_dec(v_a_292_);
lean_dec(v_val_290_);
v___x_313_ = lean_box(0);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_313_);
v___x_315_ = v___x_298_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_a_292_);
lean_dec(v_val_290_);
v_a_318_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_295_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_295_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec(v_a_286_);
lean_dec(v_a_280_);
lean_dec(v_a_275_);
v___x_326_ = lean_box(0);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_326_);
v___x_328_ = v___x_288_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_a_280_);
lean_dec(v_a_275_);
v_a_331_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_285_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_285_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_a_275_);
lean_dec_ref(v_type_266_);
lean_dec(v___x_265_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
v_a_339_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_279_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_279_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v_type_266_);
lean_dec(v___x_265_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec(v___x_262_);
lean_dec(v___x_261_);
v_a_347_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_274_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_274_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___boxed(lean_object* v___x_355_, lean_object* v___x_356_, lean_object* v___x_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_type_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v___x_2597__boxed_370_; lean_object* v_res_371_; 
v___x_2597__boxed_370_ = lean_unbox(v___x_356_);
v_res_371_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0(v___x_355_, v___x_2597__boxed_370_, v___x_357_, v___x_358_, v___x_359_, v___x_360_, v___x_361_, v_type_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(lean_object* v_u_377_, lean_object* v_type_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___f_397_; uint8_t v___x_398_; lean_object* v___x_399_; 
v___x_386_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0));
v___x_387_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1));
v___x_388_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1));
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v_u_377_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
lean_inc_ref(v___x_390_);
v___x_391_ = l_Lean_mkConst(v___x_388_, v___x_390_);
lean_inc_ref(v_type_378_);
v___x_392_ = l_Lean_Expr_app___override(v___x_391_, v_type_378_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = 0;
v___x_395_ = lean_box(0);
v___x_396_ = lean_box(v___x_394_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___boxed), 15, 8);
lean_closure_set(v___f_397_, 0, v___x_393_);
lean_closure_set(v___f_397_, 1, v___x_396_);
lean_closure_set(v___f_397_, 2, v___x_395_);
lean_closure_set(v___f_397_, 3, v___x_389_);
lean_closure_set(v___f_397_, 4, v___x_386_);
lean_closure_set(v___f_397_, 5, v___x_387_);
lean_closure_set(v___f_397_, 6, v___x_390_);
lean_closure_set(v___f_397_, 7, v_type_378_);
v___x_398_ = 0;
v___x_399_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_397_, v___x_398_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___boxed(lean_object* v_u_400_, lean_object* v_type_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_u_400_, v_type_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object* v_u_420_, lean_object* v_type_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_natModuleType_432_; lean_object* v___x_433_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1));
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v_u_420_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
lean_inc_ref(v___x_430_);
v___x_431_ = l_Lean_mkConst(v___x_428_, v___x_430_);
lean_inc_ref(v_type_421_);
v_natModuleType_432_ = l_Lean_Expr_app___override(v___x_431_, v_type_421_);
v___x_433_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_432_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_447_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_447_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_447_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_447_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
if (lean_obj_tag(v_a_434_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_del_object(v___x_436_);
v_val_438_ = lean_ctor_get(v_a_434_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_a_434_, 1);
v___x_439_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3));
v___x_440_ = l_Lean_mkConst(v___x_439_, v___x_430_);
v___x_441_ = l_Lean_mkAppB(v___x_440_, v_type_421_, v_val_438_);
v___x_442_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_441_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec(v_a_434_);
lean_dec_ref_known(v___x_430_, 2);
lean_dec_ref(v_type_421_);
v___x_443_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_443_);
v___x_445_ = v___x_436_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_430_, 2);
lean_dec_ref(v_type_421_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object* v_u_448_, lean_object* v_type_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_448_, v_type_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(lean_object* v_u_457_, lean_object* v_type_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_457_, v_type_458_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(lean_object* v_u_467_, lean_object* v_type_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(v_u_467_, v_type_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
return v_res_476_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Insts(builtin);
}
#ifdef __cplusplus
}
#endif
