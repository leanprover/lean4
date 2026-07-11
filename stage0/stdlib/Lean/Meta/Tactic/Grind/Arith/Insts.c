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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PowIdentity"};
static const lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_31_, v___y_39_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object* v_e_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(v_e_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object* v_k_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; 
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
lean_inc(v___y_59_);
lean_inc(v___y_58_);
v___x_69_ = lean_apply_11(v_k_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, lean_box(0));
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec(v___y_71_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object* v_k_83_, uint8_t v_allowLevelAssignments_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___f_96_; lean_object* v___x_97_; 
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc(v___y_85_);
v___f_96_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_96_, 0, v_k_83_);
lean_closure_set(v___f_96_, 1, v___y_85_);
lean_closure_set(v___f_96_, 2, v___y_86_);
lean_closure_set(v___f_96_, 3, v___y_87_);
lean_closure_set(v___f_96_, 4, v___y_88_);
lean_closure_set(v___f_96_, 5, v___y_89_);
lean_closure_set(v___f_96_, 6, v___y_90_);
v___x_97_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_84_, v___f_96_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
return v___x_97_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object* v_k_106_, lean_object* v_allowLevelAssignments_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_119_; lean_object* v_res_120_; 
v_allowLevelAssignments_boxed_119_ = lean_unbox(v_allowLevelAssignments_107_);
v_res_120_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_106_, v_allowLevelAssignments_boxed_119_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(lean_object* v_00_u03b1_121_, lean_object* v_k_122_, uint8_t v_allowLevelAssignments_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_122_, v_allowLevelAssignments_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object* v_00_u03b1_136_, lean_object* v_k_137_, lean_object* v_allowLevelAssignments_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_150_; lean_object* v_res_151_; 
v_allowLevelAssignments_boxed_150_ = lean_unbox(v_allowLevelAssignments_138_);
v_res_151_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_136_, v_k_137_, v_allowLevelAssignments_boxed_150_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec(v___y_139_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(lean_object* v___x_159_, uint8_t v___x_160_, lean_object* v___x_161_, lean_object* v_u_162_, lean_object* v___x_163_, lean_object* v_type_164_, lean_object* v_semiringInst_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_mkFreshExprMVar(v___x_159_, v___x_160_, v___x_161_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_charType_182_; lean_object* v___x_183_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc_n(v_a_178_, 2);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3));
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v_u_162_);
lean_ctor_set(v___x_180_, 1, v___x_163_);
v___x_181_ = l_Lean_mkConst(v___x_179_, v___x_180_);
v_charType_182_ = l_Lean_mkApp3(v___x_181_, v_type_164_, v_semiringInst_165_, v_a_178_);
v___x_183_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_charType_182_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_225_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_225_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_225_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_225_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
if (lean_obj_tag(v_a_184_) == 1)
{
lean_object* v_val_188_; lean_object* v___x_189_; lean_object* v_a_190_; lean_object* v___x_191_; 
lean_del_object(v___x_186_);
v_val_188_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_val_188_);
lean_dec_ref_known(v_a_184_, 1);
v___x_189_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_178_, v___y_173_);
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_189_);
v___x_191_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(v_a_190_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_212_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_212_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_212_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_212_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
if (lean_obj_tag(v_a_192_) == 1)
{
lean_object* v_val_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_207_; 
v_val_196_ = lean_ctor_get(v_a_192_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_207_ == 0)
{
v___x_198_ = v_a_192_;
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_val_196_);
lean_dec(v_a_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_val_188_);
lean_ctor_set(v___x_200_, 1, v_val_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_202_);
v___x_204_ = v___x_194_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec(v_a_192_);
lean_dec(v_val_188_);
v___x_208_ = lean_box(0);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_208_);
v___x_210_ = v___x_194_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_val_188_);
v_a_213_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_191_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_191_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_223_; 
lean_dec(v_a_184_);
lean_dec(v_a_178_);
v___x_221_ = lean_box(0);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_221_);
v___x_223_ = v___x_186_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec(v_a_178_);
v_a_226_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_183_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_183_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_semiringInst_165_);
lean_dec_ref(v_type_164_);
lean_dec(v___x_163_);
lean_dec(v_u_162_);
v_a_234_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_177_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_177_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_242_ = _args[0];
lean_object* v___x_243_ = _args[1];
lean_object* v___x_244_ = _args[2];
lean_object* v_u_245_ = _args[3];
lean_object* v___x_246_ = _args[4];
lean_object* v_type_247_ = _args[5];
lean_object* v_semiringInst_248_ = _args[6];
lean_object* v___y_249_ = _args[7];
lean_object* v___y_250_ = _args[8];
lean_object* v___y_251_ = _args[9];
lean_object* v___y_252_ = _args[10];
lean_object* v___y_253_ = _args[11];
lean_object* v___y_254_ = _args[12];
lean_object* v___y_255_ = _args[13];
lean_object* v___y_256_ = _args[14];
lean_object* v___y_257_ = _args[15];
lean_object* v___y_258_ = _args[16];
lean_object* v___y_259_ = _args[17];
_start:
{
uint8_t v___x_9084__boxed_260_; lean_object* v_res_261_; 
v___x_9084__boxed_260_ = lean_unbox(v___x_243_);
v_res_261_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(v___x_242_, v___x_9084__boxed_260_, v___x_244_, v_u_245_, v___x_246_, v_type_247_, v_semiringInst_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec(v___y_249_);
return v_res_261_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_box(0);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1));
v___x_267_ = l_Lean_mkConst(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2, &l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object* v_u_270_, lean_object* v_type_271_, lean_object* v_semiringInst_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___f_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3, &l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once, _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3);
v___x_286_ = 0;
v___x_287_ = lean_box(0);
v___x_288_ = lean_box(v___x_286_);
v___f_289_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed), 18, 7);
lean_closure_set(v___f_289_, 0, v___x_285_);
lean_closure_set(v___f_289_, 1, v___x_288_);
lean_closure_set(v___f_289_, 2, v___x_287_);
lean_closure_set(v___f_289_, 3, v_u_270_);
lean_closure_set(v___f_289_, 4, v___x_284_);
lean_closure_set(v___f_289_, 5, v_type_271_);
lean_closure_set(v___f_289_, 6, v_semiringInst_272_);
v___x_290_ = 0;
v___x_291_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_289_, v___x_290_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___boxed(lean_object* v_u_292_, lean_object* v_type_293_, lean_object* v_semiringInst_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_u_292_, v_type_293_, v_semiringInst_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec(v_a_295_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(lean_object* v___x_308_, uint8_t v___x_309_, lean_object* v___x_310_, lean_object* v___x_311_, lean_object* v___x_312_, lean_object* v___x_313_, lean_object* v___x_314_, lean_object* v_type_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; 
lean_inc(v___x_310_);
v___x_327_ = l_Lean_Meta_mkFreshExprMVar(v___x_308_, v___x_309_, v___x_310_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1));
v___x_330_ = l_Lean_mkConst(v___x_329_, v___x_311_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___x_332_ = l_Lean_Meta_mkFreshExprMVar(v___x_331_, v___x_309_, v___x_310_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc_n(v_a_333_, 2);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0));
v___x_335_ = l_Lean_Name_mkStr3(v___x_312_, v___x_313_, v___x_334_);
v___x_336_ = l_Lean_mkConst(v___x_335_, v___x_314_);
lean_inc(v_a_328_);
v___x_337_ = l_Lean_mkApp3(v___x_336_, v_type_315_, v_a_328_, v_a_333_);
v___x_338_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_337_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_383_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_383_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_383_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_383_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
if (lean_obj_tag(v_a_339_) == 1)
{
lean_object* v_val_343_; lean_object* v___x_344_; lean_object* v_a_345_; lean_object* v___x_346_; lean_object* v_a_347_; lean_object* v___x_348_; 
lean_del_object(v___x_341_);
v_val_343_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_a_339_, 1);
v___x_344_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_328_, v___y_323_);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v___x_344_);
v___x_346_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_333_, v___y_323_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v___x_348_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(v_a_347_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_370_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_370_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_370_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_370_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
if (lean_obj_tag(v_a_349_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_365_; 
v_val_353_ = lean_ctor_get(v_a_349_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_355_ = v_a_349_;
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_dec(v_a_349_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_a_345_);
lean_ctor_set(v___x_357_, 1, v_val_353_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_val_343_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_360_);
v___x_362_ = v___x_351_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_dec(v_a_349_);
lean_dec(v_a_345_);
lean_dec(v_val_343_);
v___x_366_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_366_);
v___x_368_ = v___x_351_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_345_);
lean_dec(v_val_343_);
v_a_371_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_348_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_348_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec(v_a_339_);
lean_dec(v_a_333_);
lean_dec(v_a_328_);
v___x_379_ = lean_box(0);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_379_);
v___x_381_ = v___x_341_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_333_);
lean_dec(v_a_328_);
v_a_384_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_338_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_338_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_a_328_);
lean_dec_ref(v_type_315_);
lean_dec(v___x_314_);
lean_dec_ref(v___x_313_);
lean_dec_ref(v___x_312_);
v_a_392_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_332_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_332_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v_type_315_);
lean_dec(v___x_314_);
lean_dec_ref(v___x_313_);
lean_dec_ref(v___x_312_);
lean_dec(v___x_311_);
lean_dec(v___x_310_);
v_a_400_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_327_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_327_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_408_ = _args[0];
lean_object* v___x_409_ = _args[1];
lean_object* v___x_410_ = _args[2];
lean_object* v___x_411_ = _args[3];
lean_object* v___x_412_ = _args[4];
lean_object* v___x_413_ = _args[5];
lean_object* v___x_414_ = _args[6];
lean_object* v_type_415_ = _args[7];
lean_object* v___y_416_ = _args[8];
lean_object* v___y_417_ = _args[9];
lean_object* v___y_418_ = _args[10];
lean_object* v___y_419_ = _args[11];
lean_object* v___y_420_ = _args[12];
lean_object* v___y_421_ = _args[13];
lean_object* v___y_422_ = _args[14];
lean_object* v___y_423_ = _args[15];
lean_object* v___y_424_ = _args[16];
lean_object* v___y_425_ = _args[17];
lean_object* v___y_426_ = _args[18];
_start:
{
uint8_t v___x_7032__boxed_427_; lean_object* v_res_428_; 
v___x_7032__boxed_427_ = lean_unbox(v___x_409_);
v_res_428_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(v___x_408_, v___x_7032__boxed_427_, v___x_410_, v___x_411_, v___x_412_, v___x_413_, v___x_414_, v_type_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec(v___y_416_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(lean_object* v_u_434_, lean_object* v_type_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___f_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0));
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1));
v___x_449_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1));
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_u_434_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_inc_ref(v___x_451_);
v___x_452_ = l_Lean_mkConst(v___x_449_, v___x_451_);
lean_inc_ref(v_type_435_);
v___x_453_ = l_Lean_Expr_app___override(v___x_452_, v_type_435_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = 0;
v___x_456_ = lean_box(0);
v___x_457_ = lean_box(v___x_455_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed), 19, 8);
lean_closure_set(v___f_458_, 0, v___x_454_);
lean_closure_set(v___f_458_, 1, v___x_457_);
lean_closure_set(v___f_458_, 2, v___x_456_);
lean_closure_set(v___f_458_, 3, v___x_450_);
lean_closure_set(v___f_458_, 4, v___x_447_);
lean_closure_set(v___f_458_, 5, v___x_448_);
lean_closure_set(v___f_458_, 6, v___x_451_);
lean_closure_set(v___f_458_, 7, v_type_435_);
v___x_459_ = 0;
v___x_460_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_458_, v___x_459_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___boxed(lean_object* v_u_461_, lean_object* v_type_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(v_u_461_, v_type_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object* v_u_485_, lean_object* v_type_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_natModuleType_497_; lean_object* v___x_498_; 
v___x_493_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1));
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v_u_485_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_inc_ref(v___x_495_);
v___x_496_ = l_Lean_mkConst(v___x_493_, v___x_495_);
lean_inc_ref(v_type_486_);
v_natModuleType_497_ = l_Lean_Expr_app___override(v___x_496_, v_type_486_);
v___x_498_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_497_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_512_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_512_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_512_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_512_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 1)
{
lean_object* v_val_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_del_object(v___x_501_);
v_val_503_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_499_, 1);
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3));
v___x_505_ = l_Lean_mkConst(v___x_504_, v___x_495_);
v___x_506_ = l_Lean_mkAppB(v___x_505_, v_type_486_, v_val_503_);
v___x_507_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_506_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_a_499_);
lean_dec_ref_known(v___x_495_, 2);
lean_dec_ref(v_type_486_);
v___x_508_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_508_);
v___x_510_ = v___x_501_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_495_, 2);
lean_dec_ref(v_type_486_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object* v_u_513_, lean_object* v_type_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_u_513_, v_type_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(lean_object* v_u_522_, lean_object* v_type_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_u_522_, v_type_523_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___boxed(lean_object* v_u_536_, lean_object* v_type_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(v_u_536_, v_type_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec(v_a_538_);
return v_res_549_;
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
