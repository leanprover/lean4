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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_Sym_sym_debug;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LawfulOrderLT"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 67, 105, 183, 31, 31, 114)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "type has `LE` and `LT`, but the `LT` instance is not lawful, failed to synthesize"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IsPreorder"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 213, 76, 156, 147, 68, 250, 139)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "type has `LE`, but is not a preorder, failed to synthesize"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "type has `LE`, but is not a partial order, failed to synthesize"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "type has `LE`, but is not a linear order, failed to synthesize"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "IsLinearPreorder"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 195, 196, 59, 47, 77, 198)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "type has `LE`, but is not a linear preorder, failed to synthesize"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_31_, v___y_35_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v_res_40_;
v_res_40_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_49_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object* v_k_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___x_58_ = lean_apply_7(v_k_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_50_ = stack[0].m_obj;
lean_object* v___y_51_ = stack[1].m_obj;
lean_object* v___y_52_ = stack[2].m_obj;
lean_object* v___y_53_ = stack[3].m_obj;
lean_object* v___y_54_ = stack[4].m_obj;
lean_object* v___y_55_ = stack[5].m_obj;
lean_object* v___y_56_ = stack[6].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_68_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object* v_k_69_, uint8_t v_allowLevelAssignments_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; 
lean_inc(v___y_72_);
lean_inc_ref(v___y_71_);
v___f_78_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_78_, 0, v_k_69_);
lean_closure_set(v___f_78_, 1, v___y_71_);
lean_closure_set(v___f_78_, 2, v___y_72_);
v___x_79_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_70_, v___f_78_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
if (lean_obj_tag(v___x_79_) == 0)
{
return v___x_79_;
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_69_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_70_ = stack[1].m_num;
lean_object* v___y_71_ = stack[2].m_obj;
lean_object* v___y_72_ = stack[3].m_obj;
lean_object* v___y_73_ = stack[4].m_obj;
lean_object* v___y_74_ = stack[5].m_obj;
lean_object* v___y_75_ = stack[6].m_obj;
lean_object* v___y_76_ = stack[7].m_obj;
lean_object* v_res_88_;
v_res_88_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_69_, v_allowLevelAssignments_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
stack->m_obj
 = v_res_88_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object* v_k_89_, lean_object* v_allowLevelAssignments_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_98_; lean_object* v_res_99_; 
v_allowLevelAssignments_boxed_98_ = lean_unbox(v_allowLevelAssignments_90_);
v_res_99_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_89_, v_allowLevelAssignments_boxed_98_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_99_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(lean_object* v_00_u03b1_100_, lean_object* v_k_101_, uint8_t v_allowLevelAssignments_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_101_, v_allowLevelAssignments_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_101_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_102_ = stack[2].m_num;
lean_object* v___y_103_ = stack[3].m_obj;
lean_object* v___y_104_ = stack[4].m_obj;
lean_object* v___y_105_ = stack[5].m_obj;
lean_object* v___y_106_ = stack[6].m_obj;
lean_object* v___y_107_ = stack[7].m_obj;
lean_object* v___y_108_ = stack[8].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(lean_box(0), v_k_101_, v_allowLevelAssignments_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object* v_00_u03b1_112_, lean_object* v_k_113_, lean_object* v_allowLevelAssignments_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_122_; lean_object* v_res_123_; 
v_allowLevelAssignments_boxed_122_ = lean_unbox(v_allowLevelAssignments_114_);
v_res_123_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_112_, v_k_113_, v_allowLevelAssignments_boxed_122_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_123_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(lean_object* v___x_131_, uint8_t v___x_132_, lean_object* v___x_133_, lean_object* v_u_134_, lean_object* v___x_135_, lean_object* v_type_136_, lean_object* v_semiringInst_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Meta_mkFreshExprMVar(v___x_131_, v___x_132_, v___x_133_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_charType_150_; lean_object* v___x_151_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc_n(v_a_146_, 2);
lean_dec_ref_known(v___x_145_, 1);
v___x_147_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3));
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v_u_134_);
lean_ctor_set(v___x_148_, 1, v___x_135_);
v___x_149_ = l_Lean_mkConst(v___x_147_, v___x_148_);
v_charType_150_ = l_Lean_mkApp3(v___x_149_, v_type_136_, v_semiringInst_137_, v_a_146_);
v___x_151_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_charType_150_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_193_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_193_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_193_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_193_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
if (lean_obj_tag(v_a_152_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_159_; 
lean_del_object(v___x_154_);
v_val_156_ = lean_ctor_get(v_a_152_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v_a_152_, 1);
v___x_157_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_146_, v___y_141_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v___x_157_);
v___x_159_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_a_158_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_180_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_180_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
if (lean_obj_tag(v_a_160_) == 1)
{
lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_175_; 
v_val_164_ = lean_ctor_get(v_a_160_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_a_160_);
if (v_isSharedCheck_175_ == 0)
{
v___x_166_ = v_a_160_;
v_isShared_167_ = v_isSharedCheck_175_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_dec(v_a_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_175_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_val_156_);
lean_ctor_set(v___x_168_, 1, v_val_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_174_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_170_);
v___x_172_ = v___x_162_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_178_; 
lean_dec(v_a_160_);
lean_dec(v_val_156_);
v___x_176_ = lean_box(0);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_176_);
v___x_178_ = v___x_162_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_val_156_);
v_a_181_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_159_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_159_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
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
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_dec(v_a_152_);
lean_dec(v_a_146_);
v___x_189_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_189_);
v___x_191_ = v___x_154_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_a_146_);
v_a_194_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_151_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_151_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_semiringInst_137_);
lean_dec_ref(v_type_136_);
lean_dec(v___x_135_);
lean_dec(v_u_134_);
v_a_202_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_145_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_145_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_131_ = stack[0].m_obj;
uint8_t v___x_132_ = stack[1].m_num;
lean_object* v___x_133_ = stack[2].m_obj;
lean_object* v_u_134_ = stack[3].m_obj;
lean_object* v___x_135_ = stack[4].m_obj;
lean_object* v_type_136_ = stack[5].m_obj;
lean_object* v_semiringInst_137_ = stack[6].m_obj;
lean_object* v___y_138_ = stack[7].m_obj;
lean_object* v___y_139_ = stack[8].m_obj;
lean_object* v___y_140_ = stack[9].m_obj;
lean_object* v___y_141_ = stack[10].m_obj;
lean_object* v___y_142_ = stack[11].m_obj;
lean_object* v___y_143_ = stack[12].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(v___x_131_, v___x_132_, v___x_133_, v_u_134_, v___x_135_, v_type_136_, v_semiringInst_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v___x_213_, lean_object* v_u_214_, lean_object* v___x_215_, lean_object* v_type_216_, lean_object* v_semiringInst_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
uint8_t v___x_3954__boxed_225_; lean_object* v_res_226_; 
v___x_3954__boxed_225_ = lean_unbox(v___x_212_);
v_res_226_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(v___x_211_, v___x_3954__boxed_225_, v___x_213_, v_u_214_, v___x_215_, v_type_216_, v_semiringInst_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1));
v___x_232_ = l_Lean_mkConst(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2, &l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once, _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object* v_u_235_, lean_object* v_type_236_, lean_object* v_semiringInst_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___f_250_; uint8_t v___x_251_; lean_object* v___x_252_; 
v___x_245_ = lean_box(0);
v___x_246_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3, &l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once, _init_l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3);
v___x_247_ = 0;
v___x_248_ = lean_box(0);
v___x_249_ = lean_box(v___x_247_);
v___f_250_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed), 14, 7);
lean_closure_set(v___f_250_, 0, v___x_246_);
lean_closure_set(v___f_250_, 1, v___x_249_);
lean_closure_set(v___f_250_, 2, v___x_248_);
lean_closure_set(v___f_250_, 3, v_u_235_);
lean_closure_set(v___f_250_, 4, v___x_245_);
lean_closure_set(v___f_250_, 5, v_type_236_);
lean_closure_set(v___f_250_, 6, v_semiringInst_237_);
v___x_251_ = 0;
v___x_252_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_250_, v___x_251_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
return v___x_252_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getIsCharInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_235_ = stack[0].m_obj;
lean_object* v_type_236_ = stack[1].m_obj;
lean_object* v_semiringInst_237_ = stack[2].m_obj;
lean_object* v_a_238_ = stack[3].m_obj;
lean_object* v_a_239_ = stack[4].m_obj;
lean_object* v_a_240_ = stack[5].m_obj;
lean_object* v_a_241_ = stack[6].m_obj;
lean_object* v_a_242_ = stack[7].m_obj;
lean_object* v_a_243_ = stack[8].m_obj;
lean_object* v_res_253_;
v_res_253_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_u_235_, v_type_236_, v_semiringInst_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(lean_object* v_u_254_, lean_object* v_type_255_, lean_object* v_semiringInst_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_u_254_, v_type_255_, v_semiringInst_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_264_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0(lean_object* v___x_266_, uint8_t v___x_267_, lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v_type_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
lean_inc(v___x_268_);
v___x_281_ = l_Lean_Meta_mkFreshExprMVar(v___x_266_, v___x_267_, v___x_268_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1));
v___x_284_ = l_Lean_mkConst(v___x_283_, v___x_269_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = l_Lean_Meta_mkFreshExprMVar(v___x_285_, v___x_267_, v___x_268_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_n(v_a_287_, 2);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___closed__0));
v___x_289_ = l_Lean_Name_mkStr3(v___x_270_, v___x_271_, v___x_288_);
v___x_290_ = l_Lean_mkConst(v___x_289_, v___x_272_);
lean_inc(v_a_282_);
v___x_291_ = l_Lean_mkApp3(v___x_290_, v_type_273_, v_a_282_, v_a_287_);
v___x_292_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_291_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_337_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_337_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_337_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_337_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
if (lean_obj_tag(v_a_293_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_302_; 
lean_del_object(v___x_295_);
v_val_297_ = lean_ctor_get(v_a_293_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v_a_293_, 1);
v___x_298_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_282_, v___y_277_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref(v___x_298_);
v___x_300_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_287_, v___y_277_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v___x_300_);
v___x_302_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_a_301_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_324_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_324_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_324_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_324_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
if (lean_obj_tag(v_a_303_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_319_; 
v_val_307_ = lean_ctor_get(v_a_303_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_a_303_);
if (v_isSharedCheck_319_ == 0)
{
v___x_309_ = v_a_303_;
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_val_307_);
lean_dec(v_a_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_a_299_);
lean_ctor_set(v___x_311_, 1, v_val_307_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_val_297_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_314_);
v___x_316_ = v___x_305_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec(v_a_303_);
lean_dec(v_a_299_);
lean_dec(v_val_297_);
v___x_320_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_320_);
v___x_322_ = v___x_305_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v_a_299_);
lean_dec(v_val_297_);
v_a_325_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_302_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_302_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec(v_a_293_);
lean_dec(v_a_287_);
lean_dec(v_a_282_);
v___x_333_ = lean_box(0);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_333_);
v___x_335_ = v___x_295_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_a_287_);
lean_dec(v_a_282_);
v_a_338_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_292_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_292_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_282_);
lean_dec_ref(v_type_273_);
lean_dec(v___x_272_);
lean_dec_ref(v___x_271_);
lean_dec_ref(v___x_270_);
v_a_346_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_286_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_286_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v_type_273_);
lean_dec(v___x_272_);
lean_dec_ref(v___x_271_);
lean_dec_ref(v___x_270_);
lean_dec(v___x_269_);
lean_dec(v___x_268_);
v_a_354_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_281_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_281_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_266_ = stack[0].m_obj;
uint8_t v___x_267_ = stack[1].m_num;
lean_object* v___x_268_ = stack[2].m_obj;
lean_object* v___x_269_ = stack[3].m_obj;
lean_object* v___x_270_ = stack[4].m_obj;
lean_object* v___x_271_ = stack[5].m_obj;
lean_object* v___x_272_ = stack[6].m_obj;
lean_object* v_type_273_ = stack[7].m_obj;
lean_object* v___y_274_ = stack[8].m_obj;
lean_object* v___y_275_ = stack[9].m_obj;
lean_object* v___y_276_ = stack[10].m_obj;
lean_object* v___y_277_ = stack[11].m_obj;
lean_object* v___y_278_ = stack[12].m_obj;
lean_object* v___y_279_ = stack[13].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0(v___x_266_, v___x_267_, v___x_268_, v___x_269_, v___x_270_, v___x_271_, v___x_272_, v_type_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___boxed(lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v___x_365_, lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v___x_368_, lean_object* v___x_369_, lean_object* v_type_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
uint8_t v___x_2597__boxed_378_; lean_object* v_res_379_; 
v___x_2597__boxed_378_ = lean_unbox(v___x_364_);
v_res_379_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0(v___x_363_, v___x_2597__boxed_378_, v___x_365_, v___x_366_, v___x_367_, v___x_368_, v___x_369_, v_type_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_379_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(lean_object* v_u_385_, lean_object* v_type_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___f_405_; uint8_t v___x_406_; lean_object* v___x_407_; 
v___x_394_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0));
v___x_395_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1));
v___x_396_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___closed__1));
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v_u_385_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
lean_inc_ref(v___x_398_);
v___x_399_ = l_Lean_mkConst(v___x_396_, v___x_398_);
lean_inc_ref(v_type_386_);
v___x_400_ = l_Lean_Expr_app___override(v___x_399_, v_type_386_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = 0;
v___x_403_ = lean_box(0);
v___x_404_ = lean_box(v___x_402_);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___lam__0___boxed), 15, 8);
lean_closure_set(v___f_405_, 0, v___x_401_);
lean_closure_set(v___f_405_, 1, v___x_404_);
lean_closure_set(v___f_405_, 2, v___x_403_);
lean_closure_set(v___f_405_, 3, v___x_397_);
lean_closure_set(v___f_405_, 4, v___x_394_);
lean_closure_set(v___f_405_, 5, v___x_395_);
lean_closure_set(v___f_405_, 6, v___x_398_);
lean_closure_set(v___f_405_, 7, v_type_386_);
v___x_406_ = 0;
v___x_407_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_405_, v___x_406_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
return v___x_407_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_385_ = stack[0].m_obj;
lean_object* v_type_386_ = stack[1].m_obj;
lean_object* v_a_387_ = stack[2].m_obj;
lean_object* v_a_388_ = stack[3].m_obj;
lean_object* v_a_389_ = stack[4].m_obj;
lean_object* v_a_390_ = stack[5].m_obj;
lean_object* v_a_391_ = stack[6].m_obj;
lean_object* v_a_392_ = stack[7].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_u_385_, v_type_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f___boxed(lean_object* v_u_409_, lean_object* v_type_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_u_409_, v_type_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_418_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object* v_u_429_, lean_object* v_type_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_natModuleType_441_; lean_object* v___x_442_; 
v___x_437_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1));
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_u_429_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
lean_inc_ref(v___x_439_);
v___x_440_ = l_Lean_mkConst(v___x_437_, v___x_439_);
lean_inc_ref(v_type_430_);
v_natModuleType_441_ = l_Lean_Expr_app___override(v___x_440_, v_type_430_);
v___x_442_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_441_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_456_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_456_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_del_object(v___x_445_);
v_val_447_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_443_, 1);
v___x_448_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3));
v___x_449_ = l_Lean_mkConst(v___x_448_, v___x_439_);
v___x_450_ = l_Lean_mkAppB(v___x_449_, v_type_430_, v_val_447_);
v___x_451_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_450_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec(v_a_443_);
lean_dec_ref_known(v___x_439_, 2);
lean_dec_ref(v_type_430_);
v___x_452_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_452_);
v___x_454_ = v___x_445_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_439_, 2);
lean_dec_ref(v_type_430_);
return v___x_442_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_429_ = stack[0].m_obj;
lean_object* v_type_430_ = stack[1].m_obj;
lean_object* v_a_431_ = stack[2].m_obj;
lean_object* v_a_432_ = stack[3].m_obj;
lean_object* v_a_433_ = stack[4].m_obj;
lean_object* v_a_434_ = stack[5].m_obj;
lean_object* v_a_435_ = stack[6].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_429_, v_type_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object* v_u_458_, lean_object* v_type_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_458_, v_type_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
return v_res_466_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(lean_object* v_u_467_, lean_object* v_type_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_467_, v_type_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_476_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_467_ = stack[0].m_obj;
lean_object* v_type_468_ = stack[1].m_obj;
lean_object* v_a_469_ = stack[2].m_obj;
lean_object* v_a_470_ = stack[3].m_obj;
lean_object* v_a_471_ = stack[4].m_obj;
lean_object* v_a_472_ = stack[5].m_obj;
lean_object* v_a_473_ = stack[6].m_obj;
lean_object* v_a_474_ = stack[7].m_obj;
lean_object* v_res_477_;
v_res_477_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(v_u_467_, v_type_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
stack->m_obj
 = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(lean_object* v_u_478_, lean_object* v_type_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(v_u_478_, v_type_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
return v_res_487_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(lean_object* v_opts_488_, lean_object* v_opt_489_){
_start:
{
lean_object* v_name_490_; lean_object* v_defValue_491_; lean_object* v_map_492_; lean_object* v___x_493_; 
v_name_490_ = lean_ctor_get(v_opt_489_, 0);
v_defValue_491_ = lean_ctor_get(v_opt_489_, 1);
v_map_492_ = lean_ctor_get(v_opts_488_, 0);
v___x_493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_492_, v_name_490_);
if (lean_obj_tag(v___x_493_) == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_unbox(v_defValue_491_);
return v___x_494_;
}
else
{
lean_object* v_val_495_; 
v_val_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_493_, 1);
if (lean_obj_tag(v_val_495_) == 1)
{
uint8_t v_v_496_; 
v_v_496_ = lean_ctor_get_uint8(v_val_495_, 0);
lean_dec_ref_known(v_val_495_, 0);
return v_v_496_;
}
else
{
uint8_t v___x_497_; 
lean_dec(v_val_495_);
v___x_497_ = lean_unbox(v_defValue_491_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_488_ = stack[0].m_obj;
lean_object* v_opt_489_ = stack[1].m_obj;
uint8_t v_res_498_;
v_res_498_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v_opts_488_, v_opt_489_);
stack->m_num = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0___boxed(lean_object* v_opts_499_, lean_object* v_opt_500_){
_start:
{
uint8_t v_res_501_; lean_object* v_r_502_; 
v_res_501_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v_opts_499_, v_opt_500_);
lean_dec_ref(v_opt_500_);
lean_dec_ref(v_opts_499_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__4(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__3));
v___x_510_ = l_Lean_stringToMessageData(v___x_509_);
return v___x_510_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object* v_u_511_, lean_object* v_type_512_, lean_object* v_ltInst_x3f_513_, lean_object* v_leInst_x3f_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
if (lean_obj_tag(v_ltInst_x3f_513_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_514_) == 1)
{
lean_object* v_val_525_; lean_object* v_val_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_lawfulOrderLTType_531_; lean_object* v___x_532_; 
v_val_525_ = lean_ctor_get(v_ltInst_x3f_513_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_ltInst_x3f_513_, 1);
v_val_526_ = lean_ctor_get(v_leInst_x3f_514_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_leInst_x3f_514_, 1);
v___x_527_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__2));
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_529_, 0, v_u_511_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_mkConst(v___x_527_, v___x_529_);
v_lawfulOrderLTType_531_ = l_Lean_mkApp3(v___x_530_, v_type_512_, v_val_525_, v_val_526_);
lean_inc_ref(v_lawfulOrderLTType_531_);
v___x_532_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_lawfulOrderLTType_531_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
if (lean_obj_tag(v_a_533_) == 1)
{
lean_dec_ref(v_lawfulOrderLTType_531_);
return v___x_532_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__4, &l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__4_once, _init_l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___closed__4);
v___x_535_ = l_Lean_indentExpr(v_lawfulOrderLTType_531_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_515_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; uint8_t v_verbose_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v_verbose_539_ = lean_ctor_get_uint8(v_a_538_, 0);
lean_dec(v_a_538_);
if (v_verbose_539_ == 0)
{
lean_dec_ref_known(v___x_536_, 2);
goto v___jp_522_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_519_);
v___x_541_ = l_Lean_Meta_Sym_sym_debug;
v___x_542_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v___x_540_, v___x_541_);
lean_dec_ref(v___x_540_);
if (v___x_542_ == 0)
{
lean_dec_ref_known(v___x_536_, 2);
goto v___jp_522_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_Sym_reportIssue(v___x_536_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_dec_ref_known(v___x_543_, 1);
goto v___jp_522_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec_ref_known(v___x_536_, 2);
v_a_552_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_537_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_537_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
else
{
lean_dec_ref(v_lawfulOrderLTType_531_);
return v___x_532_;
}
}
else
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_leInst_x3f_514_);
lean_dec_ref(v_type_512_);
lean_dec(v_u_511_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_ltInst_x3f_513_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_ltInst_x3f_513_, 0);
lean_dec(v_unused_568_);
v___x_561_ = v_ltInst_x3f_513_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_ltInst_x3f_513_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_leInst_x3f_514_);
lean_dec(v_ltInst_x3f_513_);
lean_dec_ref(v_type_512_);
lean_dec(v_u_511_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_511_ = stack[0].m_obj;
lean_object* v_type_512_ = stack[1].m_obj;
lean_object* v_ltInst_x3f_513_ = stack[2].m_obj;
lean_object* v_leInst_x3f_514_ = stack[3].m_obj;
lean_object* v_a_515_ = stack[4].m_obj;
lean_object* v_a_516_ = stack[5].m_obj;
lean_object* v_a_517_ = stack[6].m_obj;
lean_object* v_a_518_ = stack[7].m_obj;
lean_object* v_a_519_ = stack[8].m_obj;
lean_object* v_a_520_ = stack[9].m_obj;
lean_object* v_res_571_;
v_res_571_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_u_511_, v_type_512_, v_ltInst_x3f_513_, v_leInst_x3f_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f___boxed(lean_object* v_u_572_, lean_object* v_type_573_, lean_object* v_ltInst_x3f_574_, lean_object* v_leInst_x3f_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_u_572_, v_type_573_, v_ltInst_x3f_574_, v_leInst_x3f_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__2));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object* v_u_591_, lean_object* v_type_592_, lean_object* v_leInst_x3f_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_593_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_isPreorderType_609_; lean_object* v___x_610_; 
v_val_604_ = lean_ctor_get(v_leInst_x3f_593_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_leInst_x3f_593_, 1);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__1));
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v_u_591_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_mkConst(v___x_605_, v___x_607_);
v_isPreorderType_609_ = l_Lean_mkAppB(v___x_608_, v_type_592_, v_val_604_);
lean_inc_ref(v_isPreorderType_609_);
v___x_610_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isPreorderType_609_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
if (lean_obj_tag(v_a_611_) == 1)
{
lean_dec_ref(v_isPreorderType_609_);
return v___x_610_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__3, &l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__3_once, _init_l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___closed__3);
v___x_613_ = l_Lean_indentExpr(v_isPreorderType_609_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_594_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v_verbose_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v_verbose_617_ = lean_ctor_get_uint8(v_a_616_, 0);
lean_dec(v_a_616_);
if (v_verbose_617_ == 0)
{
lean_dec_ref_known(v___x_614_, 2);
goto v___jp_601_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_598_);
v___x_619_ = l_Lean_Meta_Sym_sym_debug;
v___x_620_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v___x_618_, v___x_619_);
lean_dec_ref(v___x_618_);
if (v___x_620_ == 0)
{
lean_dec_ref_known(v___x_614_, 2);
goto v___jp_601_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Sym_reportIssue(v___x_614_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_dec_ref_known(v___x_621_, 1);
goto v___jp_601_;
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref_known(v___x_614_, 2);
v_a_630_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_615_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_615_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPreorderType_609_);
return v___x_610_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_leInst_x3f_593_);
lean_dec_ref(v_type_592_);
lean_dec(v_u_591_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
v___jp_601_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_box(0);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_591_ = stack[0].m_obj;
lean_object* v_type_592_ = stack[1].m_obj;
lean_object* v_leInst_x3f_593_ = stack[2].m_obj;
lean_object* v_a_594_ = stack[3].m_obj;
lean_object* v_a_595_ = stack[4].m_obj;
lean_object* v_a_596_ = stack[5].m_obj;
lean_object* v_a_597_ = stack[6].m_obj;
lean_object* v_a_598_ = stack[7].m_obj;
lean_object* v_a_599_ = stack[8].m_obj;
lean_object* v_res_640_;
v_res_640_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_u_591_, v_type_592_, v_leInst_x3f_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f___boxed(lean_object* v_u_641_, lean_object* v_type_642_, lean_object* v_leInst_x3f_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_u_641_, v_type_642_, v_leInst_x3f_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_651_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__2));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object* v_u_659_, lean_object* v_type_660_, lean_object* v_leInst_x3f_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_661_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_isPartialOrderType_677_; lean_object* v___x_678_; 
v_val_672_ = lean_ctor_get(v_leInst_x3f_661_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_leInst_x3f_661_, 1);
v___x_673_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__1));
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v_u_659_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_mkConst(v___x_673_, v___x_675_);
v_isPartialOrderType_677_ = l_Lean_mkAppB(v___x_676_, v_type_660_, v_val_672_);
lean_inc_ref(v_isPartialOrderType_677_);
v___x_678_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isPartialOrderType_677_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
if (lean_obj_tag(v_a_679_) == 1)
{
lean_dec_ref(v_isPartialOrderType_677_);
return v___x_678_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref_known(v___x_678_, 1);
v___x_680_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__3, &l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__3_once, _init_l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___closed__3);
v___x_681_ = l_Lean_indentExpr(v_isPartialOrderType_677_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_662_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; uint8_t v_verbose_685_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v_verbose_685_ = lean_ctor_get_uint8(v_a_684_, 0);
lean_dec(v_a_684_);
if (v_verbose_685_ == 0)
{
lean_dec_ref_known(v___x_682_, 2);
goto v___jp_669_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_666_);
v___x_687_ = l_Lean_Meta_Sym_sym_debug;
v___x_688_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v___x_686_, v___x_687_);
lean_dec_ref(v___x_686_);
if (v___x_688_ == 0)
{
lean_dec_ref_known(v___x_682_, 2);
goto v___jp_669_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_Sym_reportIssue(v___x_682_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_dec_ref_known(v___x_689_, 1);
goto v___jp_669_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref_known(v___x_682_, 2);
v_a_698_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_683_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_683_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPartialOrderType_677_);
return v___x_678_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v_leInst_x3f_661_);
lean_dec_ref(v_type_660_);
lean_dec(v_u_659_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
v___jp_669_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_659_ = stack[0].m_obj;
lean_object* v_type_660_ = stack[1].m_obj;
lean_object* v_leInst_x3f_661_ = stack[2].m_obj;
lean_object* v_a_662_ = stack[3].m_obj;
lean_object* v_a_663_ = stack[4].m_obj;
lean_object* v_a_664_ = stack[5].m_obj;
lean_object* v_a_665_ = stack[6].m_obj;
lean_object* v_a_666_ = stack[7].m_obj;
lean_object* v_a_667_ = stack[8].m_obj;
lean_object* v_res_708_;
v_res_708_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_u_659_, v_type_660_, v_leInst_x3f_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f___boxed(lean_object* v_u_709_, lean_object* v_type_710_, lean_object* v_leInst_x3f_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_u_709_, v_type_710_, v_leInst_x3f_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__2));
v___x_726_ = l_Lean_stringToMessageData(v___x_725_);
return v___x_726_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(lean_object* v_u_727_, lean_object* v_type_728_, lean_object* v_leInst_x3f_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_729_) == 1)
{
lean_object* v_val_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_isLinearOrderType_745_; lean_object* v___x_746_; 
v_val_740_ = lean_ctor_get(v_leInst_x3f_729_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_leInst_x3f_729_, 1);
v___x_741_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__1));
v___x_742_ = lean_box(0);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v_u_727_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_mkConst(v___x_741_, v___x_743_);
v_isLinearOrderType_745_ = l_Lean_mkAppB(v___x_744_, v_type_728_, v_val_740_);
lean_inc_ref(v_isLinearOrderType_745_);
v___x_746_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isLinearOrderType_745_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
if (lean_obj_tag(v_a_747_) == 1)
{
lean_dec_ref(v_isLinearOrderType_745_);
return v___x_746_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__3, &l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__3_once, _init_l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___closed__3);
v___x_749_ = l_Lean_indentExpr(v_isLinearOrderType_745_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_730_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; uint8_t v_verbose_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_verbose_753_ = lean_ctor_get_uint8(v_a_752_, 0);
lean_dec(v_a_752_);
if (v_verbose_753_ == 0)
{
lean_dec_ref_known(v___x_750_, 2);
goto v___jp_737_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_734_);
v___x_755_ = l_Lean_Meta_Sym_sym_debug;
v___x_756_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v___x_754_, v___x_755_);
lean_dec_ref(v___x_754_);
if (v___x_756_ == 0)
{
lean_dec_ref_known(v___x_750_, 2);
goto v___jp_737_;
}
else
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Sym_reportIssue(v___x_750_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref_known(v___x_757_, 1);
goto v___jp_737_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref_known(v___x_750_, 2);
v_a_766_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_751_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_751_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_745_);
return v___x_746_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_leInst_x3f_729_);
lean_dec_ref(v_type_728_);
lean_dec(v_u_727_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_box(0);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_727_ = stack[0].m_obj;
lean_object* v_type_728_ = stack[1].m_obj;
lean_object* v_leInst_x3f_729_ = stack[2].m_obj;
lean_object* v_a_730_ = stack[3].m_obj;
lean_object* v_a_731_ = stack[4].m_obj;
lean_object* v_a_732_ = stack[5].m_obj;
lean_object* v_a_733_ = stack[6].m_obj;
lean_object* v_a_734_ = stack[7].m_obj;
lean_object* v_a_735_ = stack[8].m_obj;
lean_object* v_res_776_;
v_res_776_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_u_727_, v_type_728_, v_leInst_x3f_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
stack->m_obj
 = v_res_776_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f___boxed(lean_object* v_u_777_, lean_object* v_type_778_, lean_object* v_leInst_x3f_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_u_777_, v_type_778_, v_leInst_x3f_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_787_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__2));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(lean_object* v_u_795_, lean_object* v_type_796_, lean_object* v_leInst_x3f_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_797_) == 1)
{
lean_object* v_val_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_isLinearOrderType_813_; lean_object* v___x_814_; 
v_val_808_ = lean_ctor_get(v_leInst_x3f_797_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v_leInst_x3f_797_, 1);
v___x_809_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__1));
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_811_, 0, v_u_795_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_mkConst(v___x_809_, v___x_811_);
v_isLinearOrderType_813_ = l_Lean_mkAppB(v___x_812_, v_type_796_, v_val_808_);
lean_inc_ref(v_isLinearOrderType_813_);
v___x_814_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isLinearOrderType_813_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
if (lean_obj_tag(v_a_815_) == 1)
{
lean_dec_ref(v_isLinearOrderType_813_);
return v___x_814_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__3, &l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__3_once, _init_l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___closed__3);
v___x_817_ = l_Lean_indentExpr(v_isLinearOrderType_813_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_798_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; uint8_t v_verbose_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v_verbose_821_ = lean_ctor_get_uint8(v_a_820_, 0);
lean_dec(v_a_820_);
if (v_verbose_821_ == 0)
{
lean_dec_ref_known(v___x_818_, 2);
goto v___jp_805_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_822_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_802_);
v___x_823_ = l_Lean_Meta_Sym_sym_debug;
v___x_824_ = l_Lean_Option_get___at___00Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f_spec__0(v___x_822_, v___x_823_);
lean_dec_ref(v___x_822_);
if (v___x_824_ == 0)
{
lean_dec_ref_known(v___x_818_, 2);
goto v___jp_805_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_Sym_reportIssue(v___x_818_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_dec_ref_known(v___x_825_, 1);
goto v___jp_805_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref_known(v___x_818_, 2);
v_a_834_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_819_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_819_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_813_);
return v___x_814_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v_leInst_x3f_797_);
lean_dec_ref(v_type_796_);
lean_dec(v_u_795_);
v___x_842_ = lean_box(0);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
v___jp_805_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_795_ = stack[0].m_obj;
lean_object* v_type_796_ = stack[1].m_obj;
lean_object* v_leInst_x3f_797_ = stack[2].m_obj;
lean_object* v_a_798_ = stack[3].m_obj;
lean_object* v_a_799_ = stack[4].m_obj;
lean_object* v_a_800_ = stack[5].m_obj;
lean_object* v_a_801_ = stack[6].m_obj;
lean_object* v_a_802_ = stack[7].m_obj;
lean_object* v_a_803_ = stack[8].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(v_u_795_, v_type_796_, v_leInst_x3f_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f___boxed(lean_object* v_u_845_, lean_object* v_type_846_, lean_object* v_leInst_x3f_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(v_u_845_, v_type_846_, v_leInst_x3f_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_855_;
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
