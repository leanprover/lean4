// Lean compiler output
// Module: Lean.Meta.Offset
// Imports: public import Lean.Data.LBool public import Lean.Meta.Basic import Lean.Meta.NatInstTesters import Lean.Util.SafeExponentiation
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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstModNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstAdd;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
lean_object* l_OptionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_OptionT_lift___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value)} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_evalNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_evalNat___closed__0 = (const lean_object*)&l_Lean_Meta_evalNat___closed__0_value;
static const lean_string_object l_Lean_Meta_evalNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_evalNat___closed__1 = (const lean_object*)&l_Lean_Meta_evalNat___closed__1_value;
static const lean_ctor_object l_Lean_Meta_evalNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_evalNat___closed__2 = (const lean_object*)&l_Lean_Meta_evalNat___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pow"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 64, 52, 77, 166, 227, 131, 174)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mod"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(244, 133, 16, 0, 168, 19, 182, 179)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "div"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 67, 214, 176, 223, 68, 36, 94)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(124, 230, 50, 167, 103, 237, 136, 198)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(9, 137, 41, 185, 216, 152, 145, 196)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "NatPow"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17_value),LEAN_SCALAR_PTR_LITERAL(36, 252, 247, 75, 236, 16, 44, 32)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 205, 190, 14, 49, 232, 28, 251)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mod"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19_value),LEAN_SCALAR_PTR_LITERAL(141, 157, 192, 123, 66, 123, 34, 2)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(26, 140, 125, 94, 9, 215, 242, 2)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Div"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21_value),LEAN_SCALAR_PTR_LITERAL(153, 247, 56, 19, 64, 245, 190, 87)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value),LEAN_SCALAR_PTR_LITERAL(25, 78, 24, 213, 240, 238, 239, 80)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mul"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23_value),LEAN_SCALAR_PTR_LITERAL(155, 25, 183, 66, 31, 85, 84, 65)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(124, 210, 233, 157, 130, 57, 249, 157)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sub"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25_value),LEAN_SCALAR_PTR_LITERAL(203, 50, 219, 228, 204, 142, 182, 246)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(153, 170, 154, 227, 136, 99, 108, 193)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pow"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29_value),LEAN_SCALAR_PTR_LITERAL(237, 192, 51, 134, 187, 116, 61, 36)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 55, 159, 71, 164, 58, 139, 47)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_isDefEqOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_isDefEqOffset___closed__0 = (const lean_object*)&l_Lean_Meta_isDefEqOffset___closed__0_value;
static lean_once_cell_t l_Lean_Meta_isDefEqOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isDefEqOffset___closed__1;
static const lean_closure_object l_Lean_Meta_isDefEqOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_isDefEqOffset___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_isDefEqOffset___closed__2 = (const lean_object*)&l_Lean_Meta_isDefEqOffset___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object* v_e_10_, lean_object* v_k_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_toApplicative_18_; lean_object* v_toFunctor_19_; lean_object* v_toSeq_20_; lean_object* v_toSeqLeft_21_; lean_object* v_toSeqRight_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_toApplicative_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_106_; 
v___x_17_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
v_toApplicative_18_ = lean_ctor_get(v___x_17_, 0);
v_toFunctor_19_ = lean_ctor_get(v_toApplicative_18_, 0);
v_toSeq_20_ = lean_ctor_get(v_toApplicative_18_, 2);
v_toSeqLeft_21_ = lean_ctor_get(v_toApplicative_18_, 3);
v_toSeqRight_22_ = lean_ctor_get(v_toApplicative_18_, 4);
v___f_23_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
v___f_24_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_19_, 2);
v___f_25_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_25_, 0, v_toFunctor_19_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_26_, 0, v_toFunctor_19_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___f_25_);
lean_ctor_set(v___x_27_, 1, v___f_26_);
lean_inc(v_toSeqRight_22_);
v___f_28_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_28_, 0, v_toSeqRight_22_);
lean_inc(v_toSeqLeft_21_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_29_, 0, v_toSeqLeft_21_);
lean_inc(v_toSeq_20_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_30_, 0, v_toSeq_20_);
v___x_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_31_, 0, v___x_27_);
lean_ctor_set(v___x_31_, 1, v___f_23_);
lean_ctor_set(v___x_31_, 2, v___f_30_);
lean_ctor_set(v___x_31_, 3, v___f_29_);
lean_ctor_set(v___x_31_, 4, v___f_28_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___f_24_);
v___x_33_ = l_StateRefT_x27_instMonad___redArg(v___x_32_);
v_toApplicative_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_33_, 1);
lean_dec(v_unused_107_);
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_106_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_toApplicative_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_106_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v_toFunctor_38_; lean_object* v_toSeq_39_; lean_object* v_toSeqLeft_40_; lean_object* v_toSeqRight_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_104_; 
v_toFunctor_38_ = lean_ctor_get(v_toApplicative_34_, 0);
v_toSeq_39_ = lean_ctor_get(v_toApplicative_34_, 2);
v_toSeqLeft_40_ = lean_ctor_get(v_toApplicative_34_, 3);
v_toSeqRight_41_ = lean_ctor_get(v_toApplicative_34_, 4);
v_isSharedCheck_104_ = !lean_is_exclusive(v_toApplicative_34_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_dec(v_unused_105_);
v___x_43_ = v_toApplicative_34_;
v_isShared_44_ = v_isSharedCheck_104_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_toSeqRight_41_);
lean_inc(v_toSeqLeft_40_);
lean_inc(v_toSeq_39_);
lean_inc(v_toFunctor_38_);
lean_dec(v_toApplicative_34_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_104_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_54_; 
v___f_45_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
v___f_46_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_38_);
v___f_47_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_47_, 0, v_toFunctor_38_);
v___f_48_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_48_, 0, v_toFunctor_38_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___f_47_);
lean_ctor_set(v___x_49_, 1, v___f_48_);
v___f_50_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_50_, 0, v_toSeqRight_41_);
v___f_51_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_51_, 0, v_toSeqLeft_40_);
v___f_52_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_52_, 0, v_toSeq_39_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v___f_50_);
lean_ctor_set(v___x_43_, 3, v___f_51_);
lean_ctor_set(v___x_43_, 2, v___f_52_);
lean_ctor_set(v___x_43_, 1, v___f_45_);
lean_ctor_set(v___x_43_, 0, v___x_49_);
v___x_54_ = v___x_43_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___f_45_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v___f_52_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v___f_51_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v___f_50_);
v___x_54_ = v_reuseFailAlloc_103_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___f_46_);
lean_ctor_set(v___x_36_, 0, v___x_54_);
v___x_56_ = v___x_36_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___f_46_);
v___x_56_ = v_reuseFailAlloc_102_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_getMCtx_68_; lean_object* v_modifyMCtx_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_411__overap_75_; lean_object* v___x_76_; 
lean_inc_ref_n(v___x_56_, 7);
v___f_57_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_57_, 0, v___x_56_);
v___f_58_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_58_, 0, v___x_56_);
v___f_59_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_59_, 0, v___x_56_);
v___f_60_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_60_, 0, v___x_56_);
v___f_61_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_61_, 0, v___x_56_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___f_57_);
lean_ctor_set(v___x_62_, 1, v___f_58_);
v___x_63_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_63_, 0, lean_box(0));
lean_closure_set(v___x_63_, 1, v___x_56_);
v___x_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
lean_ctor_set(v___x_64_, 2, v___f_59_);
lean_ctor_set(v___x_64_, 3, v___f_60_);
lean_ctor_set(v___x_64_, 4, v___f_61_);
v___x_65_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_65_, 0, lean_box(0));
lean_closure_set(v___x_65_, 1, v___x_56_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_68_ = lean_ctor_get(v___x_67_, 0);
v_modifyMCtx_69_ = lean_ctor_get(v___x_67_, 1);
v___x_70_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_70_, 0, lean_box(0));
lean_closure_set(v___x_70_, 1, v___x_56_);
lean_inc(v_modifyMCtx_69_);
v___f_71_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_71_, 0, v_modifyMCtx_69_);
lean_closure_set(v___f_71_, 1, v___x_70_);
v___f_72_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
lean_inc(v_getMCtx_68_);
v___x_73_ = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(v___x_73_, 0, lean_box(0));
lean_closure_set(v___x_73_, 1, lean_box(0));
lean_closure_set(v___x_73_, 2, v_getMCtx_68_);
lean_closure_set(v___x_73_, 3, v___f_72_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___f_71_);
v___x_411__overap_75_ = l_Lean_instantiateMVars___redArg(v___x_66_, v___x_74_, v_e_10_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
v___x_76_ = lean_apply_5(v___x_411__overap_75_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, lean_box(0));
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_93_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_93_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_93_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_93_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
if (lean_obj_tag(v_a_77_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_83_; 
lean_dec_ref(v_k_11_);
v___x_81_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
lean_object* v_val_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_val_85_ = lean_ctor_get(v_a_77_, 0);
lean_inc(v_val_85_);
lean_dec_ref_known(v_a_77_, 1);
v___x_86_ = l_Lean_Expr_getAppFn(v_val_85_);
v___x_87_ = l_Lean_Expr_isMVar(v___x_86_);
lean_dec_ref(v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
lean_del_object(v___x_79_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
v___x_88_ = lean_apply_6(v_k_11_, v_val_85_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, lean_box(0));
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_91_; 
lean_dec(v_val_85_);
lean_dec_ref(v_k_11_);
v___x_89_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_89_);
v___x_91_ = v___x_79_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v_k_11_);
v_a_94_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_76_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_76_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_10_ = stack[0].m_obj;
lean_object* v_k_11_ = stack[1].m_obj;
lean_object* v_a_12_ = stack[2].m_obj;
lean_object* v_a_13_ = stack[3].m_obj;
lean_object* v_a_14_ = stack[4].m_obj;
lean_object* v_a_15_ = stack[5].m_obj;
lean_object* v_res_108_;
v_res_108_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(v_e_10_, v_k_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___boxed(lean_object* v_e_109_, lean_object* v_k_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(v_e_109_, v_k_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_116_;
}
}
lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* v_00_u03b1_117_, lean_object* v_e_118_, lean_object* v_k_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; lean_object* v_toApplicative_126_; lean_object* v_toFunctor_127_; lean_object* v_toSeq_128_; lean_object* v_toSeqLeft_129_; lean_object* v_toSeqRight_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_toApplicative_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_214_; 
v___x_125_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
v_toApplicative_126_ = lean_ctor_get(v___x_125_, 0);
v_toFunctor_127_ = lean_ctor_get(v_toApplicative_126_, 0);
v_toSeq_128_ = lean_ctor_get(v_toApplicative_126_, 2);
v_toSeqLeft_129_ = lean_ctor_get(v_toApplicative_126_, 3);
v_toSeqRight_130_ = lean_ctor_get(v_toApplicative_126_, 4);
v___f_131_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
v___f_132_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_127_, 2);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_133_, 0, v_toFunctor_127_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_134_, 0, v_toFunctor_127_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___f_133_);
lean_ctor_set(v___x_135_, 1, v___f_134_);
lean_inc(v_toSeqRight_130_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeqRight_130_);
lean_inc(v_toSeqLeft_129_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_137_, 0, v_toSeqLeft_129_);
lean_inc(v_toSeq_128_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_138_, 0, v_toSeq_128_);
v___x_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_139_, 0, v___x_135_);
lean_ctor_set(v___x_139_, 1, v___f_131_);
lean_ctor_set(v___x_139_, 2, v___f_138_);
lean_ctor_set(v___x_139_, 3, v___f_137_);
lean_ctor_set(v___x_139_, 4, v___f_136_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___f_132_);
v___x_141_ = l_StateRefT_x27_instMonad___redArg(v___x_140_);
v_toApplicative_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v___x_141_, 1);
lean_dec(v_unused_215_);
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_214_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_toApplicative_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_214_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_toFunctor_146_; lean_object* v_toSeq_147_; lean_object* v_toSeqLeft_148_; lean_object* v_toSeqRight_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_212_; 
v_toFunctor_146_ = lean_ctor_get(v_toApplicative_142_, 0);
v_toSeq_147_ = lean_ctor_get(v_toApplicative_142_, 2);
v_toSeqLeft_148_ = lean_ctor_get(v_toApplicative_142_, 3);
v_toSeqRight_149_ = lean_ctor_get(v_toApplicative_142_, 4);
v_isSharedCheck_212_ = !lean_is_exclusive(v_toApplicative_142_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_toApplicative_142_, 1);
lean_dec(v_unused_213_);
v___x_151_ = v_toApplicative_142_;
v_isShared_152_ = v_isSharedCheck_212_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_toSeqRight_149_);
lean_inc(v_toSeqLeft_148_);
lean_inc(v_toSeq_147_);
lean_inc(v_toFunctor_146_);
lean_dec(v_toApplicative_142_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_212_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_162_; 
v___f_153_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
v___f_154_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_146_);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_155_, 0, v_toFunctor_146_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_156_, 0, v_toFunctor_146_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___f_155_);
lean_ctor_set(v___x_157_, 1, v___f_156_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_158_, 0, v_toSeqRight_149_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_159_, 0, v_toSeqLeft_148_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_160_, 0, v_toSeq_147_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___f_158_);
lean_ctor_set(v___x_151_, 3, v___f_159_);
lean_ctor_set(v___x_151_, 2, v___f_160_);
lean_ctor_set(v___x_151_, 1, v___f_153_);
lean_ctor_set(v___x_151_, 0, v___x_157_);
v___x_162_ = v___x_151_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___f_153_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v___f_160_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v___f_159_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v___f_158_);
v___x_162_ = v_reuseFailAlloc_211_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___f_154_);
lean_ctor_set(v___x_144_, 0, v___x_162_);
v___x_164_ = v___x_144_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___f_154_);
v___x_164_ = v_reuseFailAlloc_210_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_getMCtx_176_; lean_object* v_modifyMCtx_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_453__overap_183_; lean_object* v___x_184_; 
lean_inc_ref_n(v___x_164_, 7);
v___f_165_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_165_, 0, v___x_164_);
v___f_166_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_166_, 0, v___x_164_);
v___f_167_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_167_, 0, v___x_164_);
v___f_168_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_168_, 0, v___x_164_);
v___f_169_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_169_, 0, v___x_164_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___f_165_);
lean_ctor_set(v___x_170_, 1, v___f_166_);
v___x_171_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_171_, 0, lean_box(0));
lean_closure_set(v___x_171_, 1, v___x_164_);
v___x_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_ctor_set(v___x_172_, 2, v___f_167_);
lean_ctor_set(v___x_172_, 3, v___f_168_);
lean_ctor_set(v___x_172_, 4, v___f_169_);
v___x_173_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, v___x_164_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_176_ = lean_ctor_get(v___x_175_, 0);
v_modifyMCtx_177_ = lean_ctor_get(v___x_175_, 1);
v___x_178_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_178_, 0, lean_box(0));
lean_closure_set(v___x_178_, 1, v___x_164_);
lean_inc(v_modifyMCtx_177_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_179_, 0, v_modifyMCtx_177_);
lean_closure_set(v___f_179_, 1, v___x_178_);
v___f_180_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
lean_inc(v_getMCtx_176_);
v___x_181_ = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(v___x_181_, 0, lean_box(0));
lean_closure_set(v___x_181_, 1, lean_box(0));
lean_closure_set(v___x_181_, 2, v_getMCtx_176_);
lean_closure_set(v___x_181_, 3, v___f_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___f_179_);
v___x_453__overap_183_ = l_Lean_instantiateMVars___redArg(v___x_174_, v___x_182_, v_e_118_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v_a_120_);
v___x_184_ = lean_apply_5(v___x_453__overap_183_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, lean_box(0));
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_201_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_201_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_201_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_201_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
if (lean_obj_tag(v_a_185_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_dec_ref(v_k_119_);
v___x_189_ = lean_box(0);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
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
else
{
lean_object* v_val_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_val_193_ = lean_ctor_get(v_a_185_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v_a_185_, 1);
v___x_194_ = l_Lean_Expr_getAppFn(v_val_193_);
v___x_195_ = l_Lean_Expr_isMVar(v___x_194_);
lean_dec_ref(v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_del_object(v___x_187_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v_a_120_);
v___x_196_ = lean_apply_6(v_k_119_, v_val_193_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, lean_box(0));
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_199_; 
lean_dec(v_val_193_);
lean_dec_ref(v_k_119_);
v___x_197_ = lean_box(0);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_197_);
v___x_199_ = v___x_187_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
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
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_k_119_);
v_a_202_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_184_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_184_);
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
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_118_ = stack[1].m_obj;
lean_object* v_k_119_ = stack[2].m_obj;
lean_object* v_a_120_ = stack[3].m_obj;
lean_object* v_a_121_ = stack[4].m_obj;
lean_object* v_a_122_ = stack[5].m_obj;
lean_object* v_a_123_ = stack[6].m_obj;
lean_object* v_res_216_;
v_res_216_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_box(0), v_e_118_, v_k_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___boxed(lean_object* v_00_u03b1_217_, lean_object* v_e_218_, lean_object* v_k_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(v_00_u03b1_217_, v_e_218_, v_k_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_225_;
}
}
lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(lean_object* v_e_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_321_, v_a_323_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Lean_Expr_cleanupAnnotations(v_a_331_);
v___x_333_ = l_Lean_Expr_isApp(v___x_332_);
if (v___x_333_ == 0)
{
lean_dec_ref(v___x_332_);
goto v___jp_327_;
}
else
{
lean_object* v_arg_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_arg_334_ = lean_ctor_get(v___x_332_, 1);
lean_inc_ref(v_arg_334_);
v___x_335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_332_);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
v___x_337_ = l_Lean_Expr_isConstOf(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
v___x_338_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_arg_334_);
goto v___jp_327_;
}
else
{
lean_object* v_arg_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_arg_339_ = lean_ctor_get(v___x_335_, 1);
lean_inc_ref(v_arg_339_);
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3));
v___x_342_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7));
v___x_346_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
v___x_352_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_351_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_353_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
goto v___jp_327_;
}
else
{
lean_object* v_arg_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_arg_354_ = lean_ctor_get(v___x_340_, 1);
lean_inc_ref(v_arg_354_);
v___x_355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16));
v___x_357_ = l_Lean_Expr_isConstOf(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
uint8_t v___x_358_; 
v___x_358_ = l_Lean_Expr_isApp(v___x_355_);
if (v___x_358_ == 0)
{
lean_dec_ref(v___x_355_);
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
goto v___jp_327_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_355_);
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22));
v___x_365_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24));
v___x_367_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26));
v___x_369_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
v___x_371_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_Expr_isApp(v___x_359_);
if (v___x_372_ == 0)
{
lean_dec_ref(v___x_359_);
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
goto v___jp_327_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_359_);
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30));
v___x_375_ = l_Lean_Expr_isConstOf(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_Expr_isApp(v___x_373_);
if (v___x_376_ == 0)
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
goto v___jp_327_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_373_);
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33));
v___x_379_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36));
v___x_381_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39));
v___x_383_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42));
v___x_385_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45));
v___x_387_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
v___x_389_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_388_);
lean_dec_ref(v___x_377_);
if (v___x_389_ == 0)
{
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
goto v___jp_327_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_422_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_422_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_422_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_422_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; 
v___x_395_ = lean_unbox(v_a_391_);
lean_dec(v_a_391_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_396_ = lean_box(0);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v___x_400_; 
lean_del_object(v___x_393_);
v___x_400_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
if (lean_obj_tag(v_a_401_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_400_;
}
else
{
lean_object* v_val_402_; lean_object* v___x_403_; 
lean_inc_ref(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v_val_402_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v_a_401_, 1);
v___x_403_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
if (lean_obj_tag(v_a_404_) == 0)
{
lean_dec(v_val_402_);
return v___x_403_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_420_; 
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_421_);
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
else
{
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_419_; 
v_val_408_ = lean_ctor_get(v_a_404_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_419_ == 0)
{
v___x_410_ = v_a_404_;
v_isShared_411_ = v_isSharedCheck_419_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v_a_404_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_419_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_nat_add(v_val_402_, v_val_408_);
lean_dec(v_val_408_);
lean_dec(v_val_402_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_414_);
v___x_416_ = v___x_406_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
else
{
lean_dec(v_val_402_);
return v___x_403_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_423_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_390_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_390_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v___x_377_);
v___x_431_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_463_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_463_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_463_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_463_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___x_436_; 
v___x_436_ = lean_unbox(v_a_432_);
lean_dec(v_a_432_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_439_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_437_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
else
{
lean_object* v___x_441_; 
lean_del_object(v___x_434_);
v___x_441_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
if (lean_obj_tag(v_a_442_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_441_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_444_; 
lean_inc_ref(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v_val_443_ = lean_ctor_get(v_a_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v_a_442_, 1);
v___x_444_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
if (lean_obj_tag(v_a_445_) == 0)
{
lean_dec(v_val_443_);
return v___x_444_;
}
else
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_461_; 
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_444_, 0);
lean_dec(v_unused_462_);
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_461_;
goto v_resetjp_446_;
}
else
{
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_461_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
v_val_449_ = lean_ctor_get(v_a_445_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_460_ == 0)
{
v___x_451_ = v_a_445_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v_a_445_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_nat_sub(v_val_443_, v_val_449_);
lean_dec(v_val_449_);
lean_dec(v_val_443_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_455_);
v___x_457_ = v___x_447_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
else
{
lean_dec(v_val_443_);
return v___x_444_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_441_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_464_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_431_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_431_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
else
{
lean_object* v___x_472_; 
lean_dec_ref(v___x_377_);
v___x_472_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_504_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_504_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_504_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_504_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_unbox(v_a_473_);
lean_dec(v_a_473_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_478_ = lean_box(0);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
lean_object* v___x_482_; 
lean_del_object(v___x_475_);
v___x_482_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
if (lean_obj_tag(v_a_483_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_482_;
}
else
{
lean_object* v_val_484_; lean_object* v___x_485_; 
lean_inc_ref(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v_val_484_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_val_484_);
lean_dec_ref_known(v_a_483_, 1);
v___x_485_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
if (lean_obj_tag(v_a_486_) == 0)
{
lean_dec(v_val_484_);
return v___x_485_;
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_502_; 
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_485_, 0);
lean_dec(v_unused_503_);
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_502_;
goto v_resetjp_487_;
}
else
{
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_502_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_501_; 
v_val_490_ = lean_ctor_get(v_a_486_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_a_486_);
if (v_isSharedCheck_501_ == 0)
{
v___x_492_ = v_a_486_;
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v_a_486_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_nat_mul(v_val_484_, v_val_490_);
lean_dec(v_val_490_);
lean_dec(v_val_484_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_496_);
v___x_498_ = v___x_488_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
else
{
lean_dec(v_val_484_);
return v___x_485_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_505_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_472_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_472_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
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
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v___x_377_);
v___x_513_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_545_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_545_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_545_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_545_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_519_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_519_);
v___x_521_ = v___x_516_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_object* v___x_523_; 
lean_del_object(v___x_516_);
v___x_523_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
if (lean_obj_tag(v_a_524_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_523_;
}
else
{
lean_object* v_val_525_; lean_object* v___x_526_; 
lean_inc_ref(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v_val_525_ = lean_ctor_get(v_a_524_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_a_524_, 1);
v___x_526_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
if (lean_obj_tag(v_a_527_) == 0)
{
lean_dec(v_val_525_);
return v___x_526_;
}
else
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_543_; 
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_526_, 0);
lean_dec(v_unused_544_);
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
else
{
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_val_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_542_; 
v_val_531_ = lean_ctor_get(v_a_527_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_a_527_);
if (v_isSharedCheck_542_ == 0)
{
v___x_533_ = v_a_527_;
v_isShared_534_ = v_isSharedCheck_542_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_val_531_);
lean_dec(v_a_527_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_542_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_nat_div(v_val_525_, v_val_531_);
lean_dec(v_val_531_);
lean_dec(v_val_525_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_541_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_537_);
v___x_539_ = v___x_529_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
else
{
lean_dec(v_val_525_);
return v___x_526_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_546_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_513_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_513_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec_ref(v___x_377_);
v___x_554_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_586_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_586_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_586_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_586_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_unbox(v_a_555_);
lean_dec(v_a_555_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_560_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v___x_564_; 
lean_del_object(v___x_557_);
v___x_564_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
if (lean_obj_tag(v_a_565_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_564_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_567_; 
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v_val_566_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v_a_565_, 1);
v___x_567_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
if (lean_obj_tag(v_a_568_) == 0)
{
lean_dec(v_val_566_);
return v___x_567_;
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_584_; 
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_567_, 0);
lean_dec(v_unused_585_);
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
else
{
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_583_; 
v_val_572_ = lean_ctor_get(v_a_568_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_568_);
if (v_isSharedCheck_583_ == 0)
{
v___x_574_ = v_a_568_;
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_a_568_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_nat_mod(v_val_566_, v_val_572_);
lean_dec(v_val_572_);
lean_dec(v_val_566_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_578_);
v___x_580_ = v___x_570_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
else
{
lean_dec(v_val_566_);
return v___x_567_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_587_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_554_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_554_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_object* v___x_595_; 
lean_dec_ref(v___x_377_);
v___x_595_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_606_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_601_ = lean_box(0);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v___x_605_; 
lean_del_object(v___x_598_);
v___x_605_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_339_, v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_605_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_607_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_595_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_595_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
else
{
lean_object* v___x_615_; 
lean_dec_ref(v___x_373_);
v___x_615_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_621_ = lean_box(0);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_621_);
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_625_; 
lean_del_object(v___x_618_);
v___x_625_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_339_, v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_625_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_627_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_615_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_615_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v___x_359_);
v___x_635_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_667_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_667_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_667_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_667_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint8_t v___x_640_; 
v___x_640_ = lean_unbox(v_a_636_);
lean_dec(v_a_636_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_641_ = lean_box(0);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v___x_645_; 
lean_del_object(v___x_638_);
v___x_645_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
if (lean_obj_tag(v_a_646_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_645_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_inc_ref(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v_val_647_ = lean_ctor_get(v_a_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_a_646_, 1);
v___x_648_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
if (lean_obj_tag(v_a_649_) == 0)
{
lean_dec(v_val_647_);
return v___x_648_;
}
else
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_665_; 
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v___x_648_, 0);
lean_dec(v_unused_666_);
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_665_;
goto v_resetjp_650_;
}
else
{
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_665_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
v_val_653_ = lean_ctor_get(v_a_649_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_649_);
if (v_isSharedCheck_664_ == 0)
{
v___x_655_ = v_a_649_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v_a_649_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_nat_add(v_val_647_, v_val_653_);
lean_dec(v_val_653_);
lean_dec(v_val_647_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_659_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
else
{
lean_dec(v_val_647_);
return v___x_648_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_668_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_635_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_635_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v___x_359_);
v___x_676_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_708_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_708_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_708_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_708_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
uint8_t v___x_681_; 
v___x_681_ = lean_unbox(v_a_677_);
lean_dec(v_a_677_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_682_ = lean_box(0);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v___x_686_; 
lean_del_object(v___x_679_);
v___x_686_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
if (lean_obj_tag(v_a_687_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_686_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_689_; 
lean_inc_ref(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_val_688_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_a_687_, 1);
v___x_689_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
if (lean_obj_tag(v_a_690_) == 0)
{
lean_dec(v_val_688_);
return v___x_689_;
}
else
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_706_; 
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_689_, 0);
lean_dec(v_unused_707_);
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_706_;
goto v_resetjp_691_;
}
else
{
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_706_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_val_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_705_; 
v_val_694_ = lean_ctor_get(v_a_690_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_690_);
if (v_isSharedCheck_705_ == 0)
{
v___x_696_ = v_a_690_;
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_val_694_);
lean_dec(v_a_690_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_nat_sub(v_val_688_, v_val_694_);
lean_dec(v_val_694_);
lean_dec(v_val_688_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_700_);
v___x_702_ = v___x_692_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
else
{
lean_dec(v_val_688_);
return v___x_689_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_709_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_676_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_676_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
else
{
lean_object* v___x_717_; 
lean_dec_ref(v___x_359_);
v___x_717_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_749_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_749_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_749_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_749_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
uint8_t v___x_722_; 
v___x_722_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_723_ = lean_box(0);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_727_; 
lean_del_object(v___x_720_);
v___x_727_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
if (lean_obj_tag(v_a_728_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_727_;
}
else
{
lean_object* v_val_729_; lean_object* v___x_730_; 
lean_inc_ref(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v_val_729_ = lean_ctor_get(v_a_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v_a_728_, 1);
v___x_730_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
if (lean_obj_tag(v_a_731_) == 0)
{
lean_dec(v_val_729_);
return v___x_730_;
}
else
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_747_; 
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_730_, 0);
lean_dec(v_unused_748_);
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
else
{
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_746_; 
v_val_735_ = lean_ctor_get(v_a_731_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_731_);
if (v_isSharedCheck_746_ == 0)
{
v___x_737_ = v_a_731_;
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v_a_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_nat_mul(v_val_729_, v_val_735_);
lean_dec(v_val_735_);
lean_dec(v_val_729_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_741_);
v___x_743_ = v___x_733_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
else
{
lean_dec(v_val_729_);
return v___x_730_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_750_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_717_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_717_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v___x_758_; 
lean_dec_ref(v___x_359_);
v___x_758_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_790_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_790_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_790_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_790_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_unbox(v_a_759_);
lean_dec(v_a_759_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_764_ = lean_box(0);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_764_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_768_; 
lean_del_object(v___x_761_);
v___x_768_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
if (lean_obj_tag(v_a_769_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_768_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; 
lean_inc_ref(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v_val_770_ = lean_ctor_get(v_a_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_a_769_, 1);
v___x_771_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
if (lean_obj_tag(v_a_772_) == 0)
{
lean_dec(v_val_770_);
return v___x_771_;
}
else
{
lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_771_, 0);
lean_dec(v_unused_789_);
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
else
{
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_val_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_787_; 
v_val_776_ = lean_ctor_get(v_a_772_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_787_ == 0)
{
v___x_778_ = v_a_772_;
v_isShared_779_ = v_isSharedCheck_787_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_val_776_);
lean_dec(v_a_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_787_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_nat_div(v_val_770_, v_val_776_);
lean_dec(v_val_776_);
lean_dec(v_val_770_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_782_);
v___x_784_ = v___x_774_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
else
{
lean_dec(v_val_770_);
return v___x_771_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_791_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_758_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_758_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v___x_799_; 
lean_dec_ref(v___x_359_);
v___x_799_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_831_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_831_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_831_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_831_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
uint8_t v___x_804_; 
v___x_804_ = lean_unbox(v_a_800_);
lean_dec(v_a_800_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_805_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_object* v___x_809_; 
lean_del_object(v___x_802_);
v___x_809_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
if (lean_obj_tag(v_a_810_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_809_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_812_; 
lean_inc_ref(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_val_811_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v_a_810_, 1);
v___x_812_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
if (lean_obj_tag(v_a_813_) == 0)
{
lean_dec(v_val_811_);
return v___x_812_;
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_829_; 
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_830_);
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
else
{
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_val_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_828_; 
v_val_817_ = lean_ctor_get(v_a_813_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_a_813_);
if (v_isSharedCheck_828_ == 0)
{
v___x_819_ = v_a_813_;
v_isShared_820_ = v_isSharedCheck_828_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_val_817_);
lean_dec(v_a_813_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_828_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_nat_mod(v_val_811_, v_val_817_);
lean_dec(v_val_817_);
lean_dec(v_val_811_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_827_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_823_);
v___x_825_ = v___x_815_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
else
{
lean_dec(v_val_811_);
return v___x_812_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_832_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_799_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_799_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v___x_359_);
v___x_840_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_354_, v_a_323_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_851_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_851_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_851_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_851_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; 
v___x_845_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v___x_846_ = lean_box(0);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v___x_850_; 
lean_del_object(v___x_843_);
v___x_850_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_339_, v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_850_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_334_);
v_a_852_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_840_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_840_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
lean_object* v___x_860_; 
lean_dec_ref(v___x_355_);
lean_dec_ref(v_arg_354_);
v___x_860_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_334_, v_a_323_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_871_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___x_865_; 
v___x_865_ = lean_unbox(v_a_861_);
lean_dec(v_a_861_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec_ref(v_arg_339_);
v___x_866_ = lean_box(0);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v___x_870_; 
lean_del_object(v___x_863_);
v___x_870_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_870_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_arg_339_);
v_a_872_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_860_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_860_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_880_; 
lean_dec_ref(v___x_340_);
v___x_880_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
if (lean_obj_tag(v_a_881_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_880_;
}
else
{
lean_object* v_val_882_; lean_object* v___x_883_; 
lean_inc_ref(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v_val_882_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_a_881_, 1);
v___x_883_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
if (lean_obj_tag(v_a_884_) == 0)
{
lean_dec(v_val_882_);
return v___x_883_;
}
else
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_900_; 
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_901_);
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_900_;
goto v_resetjp_885_;
}
else
{
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_900_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_val_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_899_; 
v_val_888_ = lean_ctor_get(v_a_884_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_884_);
if (v_isSharedCheck_899_ == 0)
{
v___x_890_ = v_a_884_;
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_val_888_);
lean_dec(v_a_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_nat_add(v_val_882_, v_val_888_);
lean_dec(v_val_888_);
lean_dec(v_val_882_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_894_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
else
{
lean_dec(v_val_882_);
return v___x_883_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_880_;
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec_ref(v___x_340_);
v___x_902_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
if (lean_obj_tag(v_a_903_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_902_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; 
lean_inc_ref(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_val_904_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v_a_903_, 1);
v___x_905_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
if (lean_obj_tag(v_a_906_) == 0)
{
lean_dec(v_val_904_);
return v___x_905_;
}
else
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_922_; 
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v___x_905_, 0);
lean_dec(v_unused_923_);
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_922_;
goto v_resetjp_907_;
}
else
{
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_922_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_921_; 
v_val_910_ = lean_ctor_get(v_a_906_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_906_);
if (v_isSharedCheck_921_ == 0)
{
v___x_912_ = v_a_906_;
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v_a_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_nat_sub(v_val_904_, v_val_910_);
lean_dec(v_val_910_);
lean_dec(v_val_904_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_916_);
v___x_918_ = v___x_908_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
else
{
lean_dec(v_val_904_);
return v___x_905_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_902_;
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec_ref(v___x_340_);
v___x_924_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
if (lean_obj_tag(v_a_925_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_924_;
}
else
{
lean_object* v_val_926_; lean_object* v___x_927_; 
lean_inc_ref(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_val_926_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_val_926_);
lean_dec_ref_known(v_a_925_, 1);
v___x_927_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
if (lean_obj_tag(v_a_928_) == 0)
{
lean_dec(v_val_926_);
return v___x_927_;
}
else
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_944_; 
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_945_);
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_944_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_944_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_943_; 
v_val_932_ = lean_ctor_get(v_a_928_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_943_ == 0)
{
v___x_934_ = v_a_928_;
v_isShared_935_ = v_isSharedCheck_943_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_dec(v_a_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_943_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_nat_mul(v_val_926_, v_val_932_);
lean_dec(v_val_932_);
lean_dec(v_val_926_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_938_);
v___x_940_ = v___x_930_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
else
{
lean_dec(v_val_926_);
return v___x_927_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_924_;
}
}
}
else
{
lean_object* v___x_946_; 
lean_dec_ref(v___x_340_);
v___x_946_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
if (lean_obj_tag(v_a_947_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_946_;
}
else
{
lean_object* v_val_948_; lean_object* v___x_949_; 
lean_inc_ref(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v_val_948_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v_a_947_, 1);
v___x_949_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
if (lean_obj_tag(v_a_950_) == 0)
{
lean_dec(v_val_948_);
return v___x_949_;
}
else
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_966_; 
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_949_, 0);
lean_dec(v_unused_967_);
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_966_;
goto v_resetjp_951_;
}
else
{
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_966_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_val_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_965_; 
v_val_954_ = lean_ctor_get(v_a_950_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_965_ == 0)
{
v___x_956_ = v_a_950_;
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_val_954_);
lean_dec(v_a_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = lean_nat_div(v_val_948_, v_val_954_);
lean_dec(v_val_954_);
lean_dec(v_val_948_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_960_);
v___x_962_ = v___x_952_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
else
{
lean_dec(v_val_948_);
return v___x_949_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_946_;
}
}
}
else
{
lean_object* v___x_968_; 
lean_dec_ref(v___x_340_);
v___x_968_ = l_Lean_Meta_evalNat(v_arg_339_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
if (lean_obj_tag(v_a_969_) == 0)
{
lean_dec_ref(v_arg_334_);
return v___x_968_;
}
else
{
lean_object* v_val_970_; lean_object* v___x_971_; 
lean_inc_ref(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v_val_970_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v_a_969_, 1);
v___x_971_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
if (lean_obj_tag(v_a_972_) == 0)
{
lean_dec(v_val_970_);
return v___x_971_;
}
else
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_988_; 
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_971_, 0);
lean_dec(v_unused_989_);
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
else
{
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_val_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_987_; 
v_val_976_ = lean_ctor_get(v_a_972_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_987_ == 0)
{
v___x_978_ = v_a_972_;
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_val_976_);
lean_dec(v_a_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_nat_mod(v_val_970_, v_val_976_);
lean_dec(v_val_976_);
lean_dec(v_val_970_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_982_);
v___x_984_ = v___x_974_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
else
{
lean_dec(v_val_970_);
return v___x_971_;
}
}
}
else
{
lean_dec_ref(v_arg_334_);
return v___x_968_;
}
}
}
else
{
lean_object* v___x_990_; 
lean_dec_ref(v___x_340_);
v___x_990_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_339_, v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_990_;
}
}
}
else
{
lean_object* v___x_991_; 
lean_dec_ref(v___x_335_);
v___x_991_ = l_Lean_Meta_evalNat(v_arg_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
if (lean_obj_tag(v_a_992_) == 0)
{
return v___x_991_;
}
else
{
lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1010_);
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1009_;
goto v_resetjp_993_;
}
else
{
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1009_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_val_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1008_; 
v_val_996_ = lean_ctor_get(v_a_992_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_992_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_998_ = v_a_992_;
v_isShared_999_ = v_isSharedCheck_1008_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_val_996_);
lean_dec(v_a_992_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1008_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_add(v_val_996_, v___x_1000_);
lean_dec(v_val_996_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1003_);
v___x_1005_ = v___x_994_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_330_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_330_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
v___jp_327_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_321_ = stack[0].m_obj;
lean_object* v_a_322_ = stack[1].m_obj;
lean_object* v_a_323_ = stack[2].m_obj;
lean_object* v_a_324_ = stack[3].m_obj;
lean_object* v_a_325_ = stack[4].m_obj;
lean_object* v_res_1019_;
v_res_1019_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
stack->m_obj
 = v_res_1019_;
}
lean_object* l_Lean_Meta_evalNat(lean_object* v_e_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
switch(lean_obj_tag(v_e_1020_))
{
case 9:
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v_e_1020_, 0);
lean_inc_ref(v_a_1029_);
lean_dec_ref_known(v_e_1020_, 1);
if (lean_obj_tag(v_a_1029_) == 0)
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_val_1030_ = lean_ctor_get(v_a_1029_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v_a_1029_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v_a_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 1);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_val_1030_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
else
{
lean_dec_ref(v_a_1029_);
goto v___jp_1026_;
}
}
case 10:
{
lean_object* v_expr_1039_; 
v_expr_1039_ = lean_ctor_get(v_e_1020_, 1);
lean_inc_ref(v_expr_1039_);
lean_dec_ref_known(v_e_1020_, 2);
v_e_1020_ = v_expr_1039_;
goto _start;
}
case 4:
{
lean_object* v_declName_1041_; 
v_declName_1041_ = lean_ctor_get(v_e_1020_, 0);
lean_inc(v_declName_1041_);
lean_dec_ref_known(v_e_1020_, 2);
if (lean_obj_tag(v_declName_1041_) == 1)
{
lean_object* v_pre_1042_; 
v_pre_1042_ = lean_ctor_get(v_declName_1041_, 0);
lean_inc(v_pre_1042_);
if (lean_obj_tag(v_pre_1042_) == 1)
{
lean_object* v_pre_1043_; 
v_pre_1043_ = lean_ctor_get(v_pre_1042_, 0);
if (lean_obj_tag(v_pre_1043_) == 0)
{
lean_object* v_str_1044_; lean_object* v_str_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_str_1044_ = lean_ctor_get(v_declName_1041_, 1);
lean_inc_ref(v_str_1044_);
lean_dec_ref_known(v_declName_1041_, 2);
v_str_1045_ = lean_ctor_get(v_pre_1042_, 1);
lean_inc_ref(v_str_1045_);
lean_dec_ref_known(v_pre_1042_, 2);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__0));
v___x_1047_ = lean_string_dec_eq(v_str_1045_, v___x_1046_);
lean_dec_ref(v_str_1045_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v_str_1044_);
goto v___jp_1026_;
}
else
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__1));
v___x_1049_ = lean_string_dec_eq(v_str_1044_, v___x_1048_);
lean_dec_ref(v_str_1044_);
if (v___x_1049_ == 0)
{
goto v___jp_1026_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__2));
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
else
{
lean_dec_ref_known(v_pre_1042_, 2);
lean_dec_ref_known(v_declName_1041_, 2);
goto v___jp_1026_;
}
}
else
{
lean_dec_ref_known(v_declName_1041_, 2);
lean_dec(v_pre_1042_);
goto v___jp_1026_;
}
}
else
{
lean_dec(v_declName_1041_);
goto v___jp_1026_;
}
}
case 5:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
return v___x_1052_;
}
case 2:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
return v___x_1053_;
}
default: 
{
lean_dec_ref(v_e_1020_);
goto v___jp_1026_;
}
}
v___jp_1026_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_evalNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1020_ = stack[0].m_obj;
lean_object* v_a_1021_ = stack[1].m_obj;
lean_object* v_a_1022_ = stack[2].m_obj;
lean_object* v_a_1023_ = stack[3].m_obj;
lean_object* v_a_1024_ = stack[4].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l_Lean_Meta_evalNat(v_e_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
stack->m_obj
 = v_res_1054_;
}
lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(lean_object* v_b_1055_, lean_object* v_n_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_evalNat(v_n_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
if (lean_obj_tag(v_a_1063_) == 0)
{
lean_dec_ref(v_b_1055_);
return v___x_1062_;
}
else
{
lean_object* v_val_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
lean_inc_ref(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v_val_1064_ = lean_ctor_get(v_a_1063_, 0);
lean_inc_n(v_val_1064_, 2);
lean_dec_ref_known(v_a_1063_, 1);
v___x_1065_ = 1;
v___x_1066_ = l_Lean_checkExponent(v_val_1064_, v___x_1065_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1095_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1095_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1095_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_unbox(v_a_1067_);
lean_dec(v_a_1067_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_dec(v_val_1064_);
lean_dec_ref(v_b_1055_);
v___x_1072_ = lean_box(0);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1072_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v___x_1076_; 
lean_del_object(v___x_1069_);
v___x_1076_ = l_Lean_Meta_evalNat(v_b_1055_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
if (lean_obj_tag(v_a_1077_) == 0)
{
lean_dec(v_val_1064_);
return v___x_1076_;
}
else
{
lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1076_, 0);
lean_dec(v_unused_1094_);
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1093_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1093_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_val_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1092_; 
v_val_1081_ = lean_ctor_get(v_a_1077_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1083_ = v_a_1077_;
v_isShared_1084_ = v_isSharedCheck_1092_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_val_1081_);
lean_dec(v_a_1077_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1092_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_nat_pow(v_val_1081_, v_val_1064_);
lean_dec(v_val_1064_);
lean_dec(v_val_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1087_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1064_);
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_val_1064_);
lean_dec_ref(v_b_1055_);
v_a_1096_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1066_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1066_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_1055_);
return v___x_1062_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1055_ = stack[0].m_obj;
lean_object* v_n_1056_ = stack[1].m_obj;
lean_object* v_a_1057_ = stack[2].m_obj;
lean_object* v_a_1058_ = stack[3].m_obj;
lean_object* v_a_1059_ = stack[4].m_obj;
lean_object* v_a_1060_ = stack[5].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_b_1055_, v_n_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(lean_object* v_b_1105_, lean_object* v_n_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_b_1105_, v_n_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_evalNat(v_e_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(lean_object* v_e_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
return v_res_1126_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(lean_object* v_k_1127_, uint8_t v_allowLevelAssignments_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1128_, v_k_1127_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1134_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1134_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1127_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_1128_ = stack[1].m_num;
lean_object* v___y_1129_ = stack[2].m_obj;
lean_object* v___y_1130_ = stack[3].m_obj;
lean_object* v___y_1131_ = stack[4].m_obj;
lean_object* v___y_1132_ = stack[5].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v_k_1127_, v_allowLevelAssignments_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object* v_k_1152_, lean_object* v_allowLevelAssignments_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1159_; lean_object* v_res_1160_; 
v_allowLevelAssignments_boxed_1159_ = lean_unbox(v_allowLevelAssignments_1153_);
v_res_1160_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v_k_1152_, v_allowLevelAssignments_boxed_1159_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1160_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_object* v_00_u03b1_1161_, lean_object* v_k_1162_, uint8_t v_allowLevelAssignments_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v_k_1162_, v_allowLevelAssignments_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1162_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_1163_ = stack[2].m_num;
lean_object* v___y_1164_ = stack[3].m_obj;
lean_object* v___y_1165_ = stack[4].m_obj;
lean_object* v___y_1166_ = stack[5].m_obj;
lean_object* v___y_1167_ = stack[6].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_box(0), v_k_1162_, v_allowLevelAssignments_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_k_1172_, lean_object* v_allowLevelAssignments_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1179_; lean_object* v_res_1180_; 
v_allowLevelAssignments_boxed_1179_ = lean_unbox(v_allowLevelAssignments_1173_);
v_res_1180_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(v_00_u03b1_1171_, v_k_1172_, v_allowLevelAssignments_boxed_1179_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1180_;
}
}
lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t v___x_1181_, lean_object* v_e_1182_, lean_object* v_inst_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___y_1190_; lean_object* v___x_1207_; uint8_t v_transparency_1208_; uint8_t v___x_1209_; 
v___x_1207_ = l_Lean_Meta_Context_config(v___y_1184_);
v_transparency_1208_ = lean_ctor_get_uint8(v___x_1207_, 9);
lean_dec_ref(v___x_1207_);
v___x_1209_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1208_, v___x_1181_);
if (v___x_1209_ == 0)
{
lean_object* v_keyedConfig_1210_; uint8_t v_trackZetaDelta_1211_; lean_object* v_zetaDeltaSet_1212_; lean_object* v_lctx_1213_; lean_object* v_localInstances_1214_; lean_object* v_defEqCtx_x3f_1215_; lean_object* v_synthPendingDepth_1216_; lean_object* v_customCanUnfoldPredicate_x3f_1217_; uint8_t v_univApprox_1218_; uint8_t v_inTypeClassResolution_1219_; uint8_t v_cacheInferType_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1229_; 
v_keyedConfig_1210_ = lean_ctor_get(v___y_1184_, 0);
v_trackZetaDelta_1211_ = lean_ctor_get_uint8(v___y_1184_, sizeof(void*)*7);
v_zetaDeltaSet_1212_ = lean_ctor_get(v___y_1184_, 1);
v_lctx_1213_ = lean_ctor_get(v___y_1184_, 2);
v_localInstances_1214_ = lean_ctor_get(v___y_1184_, 3);
v_defEqCtx_x3f_1215_ = lean_ctor_get(v___y_1184_, 4);
v_synthPendingDepth_1216_ = lean_ctor_get(v___y_1184_, 5);
v_customCanUnfoldPredicate_x3f_1217_ = lean_ctor_get(v___y_1184_, 6);
v_univApprox_1218_ = lean_ctor_get_uint8(v___y_1184_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1219_ = lean_ctor_get_uint8(v___y_1184_, sizeof(void*)*7 + 2);
v_cacheInferType_1220_ = lean_ctor_get_uint8(v___y_1184_, sizeof(void*)*7 + 3);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1222_ = v___y_1184_;
v_isShared_1223_ = v_isSharedCheck_1229_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1217_);
lean_inc(v_synthPendingDepth_1216_);
lean_inc(v_defEqCtx_x3f_1215_);
lean_inc(v_localInstances_1214_);
lean_inc(v_lctx_1213_);
lean_inc(v_zetaDeltaSet_1212_);
lean_inc(v_keyedConfig_1210_);
lean_dec(v___y_1184_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1229_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1181_, v_keyedConfig_1210_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_zetaDeltaSet_1212_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_lctx_1213_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_localInstances_1214_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_defEqCtx_x3f_1215_);
lean_ctor_set(v_reuseFailAlloc_1228_, 5, v_synthPendingDepth_1216_);
lean_ctor_set(v_reuseFailAlloc_1228_, 6, v_customCanUnfoldPredicate_x3f_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*7, v_trackZetaDelta_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*7 + 1, v_univApprox_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*7 + 3, v_cacheInferType_1220_);
v___x_1226_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_isExprDefEq(v_e_1182_, v_inst_1183_, v___x_1226_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v___x_1226_);
v___y_1190_ = v___x_1227_;
goto v___jp_1189_;
}
}
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Meta_isExprDefEq(v_e_1182_, v_inst_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v___y_1184_);
v___y_1190_ = v___x_1230_;
goto v___jp_1189_;
}
v___jp_1189_:
{
if (lean_obj_tag(v___y_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___y_1190_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___y_1190_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___y_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_a_1199_ = lean_ctor_get(v___y_1190_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___y_1190_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___y_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchesInstance___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1181_ = stack[0].m_num;
lean_object* v_e_1182_ = stack[1].m_obj;
lean_object* v_inst_1183_ = stack[2].m_obj;
lean_object* v___y_1184_ = stack[3].m_obj;
lean_object* v___y_1185_ = stack[4].m_obj;
lean_object* v___y_1186_ = stack[5].m_obj;
lean_object* v___y_1187_ = stack[6].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l_Lean_Meta_matchesInstance___lam__0(v___x_1181_, v_e_1182_, v_inst_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object* v___x_1232_, lean_object* v_e_1233_, lean_object* v_inst_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v___x_670__boxed_1240_; lean_object* v_res_1241_; 
v___x_670__boxed_1240_ = lean_unbox(v___x_1232_);
v_res_1241_ = l_Lean_Meta_matchesInstance___lam__0(v___x_670__boxed_1240_, v_e_1233_, v_inst_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
return v_res_1241_;
}
}
lean_object* l_Lean_Meta_matchesInstance(lean_object* v_e_1242_, lean_object* v_inst_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1249_ = 3;
v___x_1250_ = lean_box(v___x_1249_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Meta_matchesInstance___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1251_, 0, v___x_1250_);
lean_closure_set(v___f_1251_, 1, v_e_1242_);
lean_closure_set(v___f_1251_, 2, v_inst_1243_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___f_1251_, v___x_1252_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v___x_1253_;
}
}
LEAN_EXPORT void l_Lean_Meta_matchesInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1242_ = stack[0].m_obj;
lean_object* v_inst_1243_ = stack[1].m_obj;
lean_object* v_a_1244_ = stack[2].m_obj;
lean_object* v_a_1245_ = stack[3].m_obj;
lean_object* v_a_1246_ = stack[4].m_obj;
lean_object* v_a_1247_ = stack[5].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l_Lean_Meta_matchesInstance(v_e_1242_, v_inst_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___boxed(lean_object* v_e_1255_, lean_object* v_inst_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_matchesInstance(v_e_1255_, v_inst_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1262_;
}
}
lean_object* l_Lean_Meta_isOffset_x3f(lean_object* v_e_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_a_1270_; lean_object* v_b_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1263_, v_a_1265_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = l_Lean_Expr_cleanupAnnotations(v_a_1333_);
v___x_1335_ = l_Lean_Expr_isApp(v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v___x_1334_);
goto v___jp_1329_;
}
else
{
lean_object* v_arg_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_arg_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc_ref(v_arg_1336_);
v___x_1337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1334_);
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
v___x_1339_ = l_Lean_Expr_isConstOf(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_Expr_isApp(v___x_1337_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_arg_1336_);
goto v___jp_1329_;
}
else
{
lean_object* v_arg_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_arg_1341_ = lean_ctor_get(v___x_1337_, 1);
lean_inc_ref(v_arg_1341_);
v___x_1342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1337_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
v___x_1344_ = l_Lean_Expr_isConstOf(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_Expr_isApp(v___x_1342_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
goto v___jp_1329_;
}
else
{
lean_object* v_arg_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_arg_1346_ = lean_ctor_get(v___x_1342_, 1);
lean_inc_ref(v_arg_1346_);
v___x_1347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1342_);
v___x_1348_ = l_Lean_Expr_isApp(v___x_1347_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v___x_1347_);
lean_dec_ref(v_arg_1346_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
goto v___jp_1329_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1347_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
v___x_1351_ = l_Lean_Expr_isConstOf(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Lean_Expr_isApp(v___x_1349_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1349_);
lean_dec_ref(v_arg_1346_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
goto v___jp_1329_;
}
else
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1349_);
v___x_1354_ = l_Lean_Expr_isApp(v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v___x_1353_);
lean_dec_ref(v_arg_1346_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
goto v___jp_1329_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1353_);
v___x_1356_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
v___x_1357_ = l_Lean_Expr_isConstOf(v___x_1355_, v___x_1356_);
lean_dec_ref(v___x_1355_);
if (v___x_1357_ == 0)
{
lean_dec_ref(v_arg_1346_);
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
goto v___jp_1329_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = l_Lean_Nat_mkInstHAdd;
v___x_1359_ = l_Lean_Meta_matchesInstance(v_arg_1346_, v___x_1358_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1369_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1369_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1369_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_unbox(v_a_1360_);
lean_dec(v_a_1360_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
v___x_1365_ = lean_box(0);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_del_object(v___x_1362_);
v_a_1270_ = v_arg_1341_;
v_b_1271_ = v_arg_1336_;
v___y_1272_ = v_a_1264_;
v___y_1273_ = v_a_1265_;
v___y_1274_ = v_a_1266_;
v___y_1275_ = v_a_1267_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
v_a_1370_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1359_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1359_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec_ref(v___x_1349_);
v___x_1378_ = l_Lean_Nat_mkInstAdd;
v___x_1379_ = l_Lean_Meta_matchesInstance(v_arg_1346_, v___x_1378_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1389_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_unbox(v_a_1380_);
lean_dec(v_a_1380_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
v___x_1385_ = lean_box(0);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_del_object(v___x_1382_);
v_a_1270_ = v_arg_1341_;
v_b_1271_ = v_arg_1336_;
v___y_1272_ = v_a_1264_;
v___y_1273_ = v_a_1265_;
v___y_1274_ = v_a_1266_;
v___y_1275_ = v_a_1267_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_arg_1341_);
lean_dec_ref(v_arg_1336_);
v_a_1390_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1379_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1379_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1342_);
v_a_1270_ = v_arg_1341_;
v_b_1271_ = v_arg_1336_;
v___y_1272_ = v_a_1264_;
v___y_1273_ = v_a_1265_;
v___y_1274_ = v_a_1266_;
v___y_1275_ = v_a_1267_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v___x_1398_; 
lean_dec_ref(v___x_1337_);
v___x_1398_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_arg_1336_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1418_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1417_; 
v_fst_1403_ = lean_ctor_get(v_a_1399_, 0);
v_snd_1404_ = lean_ctor_get(v_a_1399_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_a_1399_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1406_ = v_a_1399_;
v_isShared_1407_ = v_isSharedCheck_1417_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_a_1399_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1417_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v_snd_1404_, v___x_1408_);
lean_dec(v_snd_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1409_);
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1412_);
v___x_1414_ = v___x_1401_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_a_1419_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1398_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1398_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1332_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1332_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
v___jp_1269_:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_evalNat(v_b_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1320_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1320_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1320_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
if (lean_obj_tag(v_a_1277_) == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec_ref(v_a_1270_);
v___x_1281_ = lean_box(0);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1279_);
v_val_1285_ = lean_ctor_get(v_a_1277_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1277_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1287_ = v_a_1277_;
v_isShared_1288_ = v_isSharedCheck_1319_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v_a_1277_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1319_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; 
v___x_1289_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_a_1270_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1310_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1310_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1310_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1309_; 
v_fst_1294_ = lean_ctor_get(v_a_1290_, 0);
v_snd_1295_ = lean_ctor_get(v_a_1290_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_a_1290_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1297_ = v_a_1290_;
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v_a_1290_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_nat_add(v_snd_1295_, v_val_1285_);
lean_dec(v_val_1285_);
lean_dec(v_snd_1295_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_fst_1294_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1301_);
v___x_1303_ = v___x_1287_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1303_);
v___x_1305_ = v___x_1292_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_del_object(v___x_1287_);
lean_dec(v_val_1285_);
v_a_1311_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1289_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1289_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_a_1270_);
v_a_1321_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1276_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1276_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
v___jp_1329_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_isOffset_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1263_ = stack[0].m_obj;
lean_object* v_a_1264_ = stack[1].m_obj;
lean_object* v_a_1265_ = stack[2].m_obj;
lean_object* v_a_1266_ = stack[3].m_obj;
lean_object* v_a_1267_ = stack[4].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_Meta_isOffset_x3f(v_e_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
stack->m_obj
 = v_res_1435_;
}
lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* v_e_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1442_; 
lean_inc_ref(v_e_1436_);
v___x_1442_ = l_Lean_Meta_isOffset_x3f(v_e_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1456_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
if (lean_obj_tag(v_a_1443_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_e_1436_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1448_);
v___x_1450_ = v___x_1445_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
lean_object* v_val_1452_; lean_object* v___x_1454_; 
lean_dec_ref(v_e_1436_);
v_val_1452_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_val_1452_);
lean_dec_ref_known(v_a_1443_, 1);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_val_1452_);
v___x_1454_ = v___x_1445_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_e_1436_);
v_a_1457_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1442_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1442_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1436_ = stack[0].m_obj;
lean_object* v_a_1437_ = stack[1].m_obj;
lean_object* v_a_1438_ = stack[2].m_obj;
lean_object* v_a_1439_ = stack[3].m_obj;
lean_object* v_a_1440_ = stack[4].m_obj;
lean_object* v_res_1465_;
v_res_1465_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_e_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
stack->m_obj
 = v_res_1465_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object* v_e_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_e_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f___boxed(lean_object* v_e_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_isOffset_x3f(v_e_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
return v_res_1479_;
}
}
lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Meta_evalNat(v_e_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1503_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1503_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1503_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
if (lean_obj_tag(v_a_1487_) == 1)
{
lean_object* v_val_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v_val_1491_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v_a_1487_, 1);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_nat_dec_eq(v_val_1491_, v___x_1492_);
lean_dec(v_val_1491_);
v___x_1494_ = lean_box(v___x_1493_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1494_);
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec(v_a_1487_);
v___x_1498_ = 0;
v___x_1499_ = lean_box(v___x_1498_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1499_);
v___x_1501_ = v___x_1489_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1486_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1486_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1480_ = stack[0].m_obj;
lean_object* v_a_1481_ = stack[1].m_obj;
lean_object* v_a_1482_ = stack[2].m_obj;
lean_object* v_a_1483_ = stack[3].m_obj;
lean_object* v_a_1484_ = stack[4].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1519_;
}
}
lean_object* l_Lean_Meta_mkOffset(lean_object* v_e_1520_, lean_object* v_offset_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_nat_dec_eq(v_offset_1521_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc_ref(v_e_1520_);
v___x_1529_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1520_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1544_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_unbox(v_a_1530_);
lean_dec(v_a_1530_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = l_Lean_mkNatLit(v_offset_1521_);
v___x_1536_ = l_Lean_mkNatAdd(v_e_1520_, v___x_1535_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1538_ = v___x_1532_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_dec_ref(v_e_1520_);
v___x_1540_ = l_Lean_mkNatLit(v_offset_1521_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1540_);
v___x_1542_ = v___x_1532_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_offset_1521_);
lean_dec_ref(v_e_1520_);
v_a_1545_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1529_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1529_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v___x_1553_; 
lean_dec(v_offset_1521_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_e_1520_);
return v___x_1553_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1520_ = stack[0].m_obj;
lean_object* v_offset_1521_ = stack[1].m_obj;
lean_object* v_a_1522_ = stack[2].m_obj;
lean_object* v_a_1523_ = stack[3].m_obj;
lean_object* v_a_1524_ = stack[4].m_obj;
lean_object* v_a_1525_ = stack[5].m_obj;
lean_object* v_res_1554_;
v_res_1554_ = l_Lean_Meta_mkOffset(v_e_1520_, v_offset_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
stack->m_obj
 = v_res_1554_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOffset___boxed(lean_object* v_e_1555_, lean_object* v_offset_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Meta_mkOffset(v_e_1555_, v_offset_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
return v_res_1562_;
}
}
lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object* v_s_1563_, lean_object* v_t_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_is_expr_def_eq(v_s_1563_, v_t_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1581_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1581_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1581_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1575_ = lean_unbox(v_a_1571_);
lean_dec(v_a_1571_);
v___x_1576_ = l_Lean_Bool_toLBool(v___x_1575_);
v___x_1577_ = lean_box(v___x_1576_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1579_ = v___x_1573_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1570_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1570_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isDefEqOffset___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1563_ = stack[0].m_obj;
lean_object* v_t_1564_ = stack[1].m_obj;
lean_object* v___y_1565_ = stack[2].m_obj;
lean_object* v___y_1566_ = stack[3].m_obj;
lean_object* v___y_1567_ = stack[4].m_obj;
lean_object* v___y_1568_ = stack[5].m_obj;
lean_object* v_res_1590_;
v_res_1590_ = l_Lean_Meta_isDefEqOffset___lam__0(v_s_1563_, v_t_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
stack->m_obj
 = v_res_1590_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0___boxed(lean_object* v_s_1591_, lean_object* v_t_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_isDefEqOffset___lam__0(v_s_1591_, v_t_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v_res_1598_;
}
}
lean_object* l_Lean_Meta_isDefEqOffset___lam__1(uint8_t v___x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_box(v___x_1599_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT void l_Lean_Meta_isDefEqOffset___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1599_ = stack[0].m_num;
lean_object* v___y_1600_ = stack[1].m_obj;
lean_object* v___y_1601_ = stack[2].m_obj;
lean_object* v___y_1602_ = stack[3].m_obj;
lean_object* v___y_1603_ = stack[4].m_obj;
lean_object* v_res_1607_;
v_res_1607_ = l_Lean_Meta_isDefEqOffset___lam__1(v___x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1___boxed(lean_object* v___x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
uint8_t v___x_3226__boxed_1614_; lean_object* v_res_1615_; 
v___x_3226__boxed_1614_ = lean_unbox(v___x_1608_);
v_res_1615_ = l_Lean_Meta_isDefEqOffset___lam__1(v___x_3226__boxed_1614_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1615_;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_box(0);
v___x_1619_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__0));
v___x_1620_ = l_Lean_mkConst(v___x_1619_, v___x_1618_);
return v___x_1620_;
}
}
lean_object* l_Lean_Meta_isDefEqOffset(lean_object* v_s_1624_, lean_object* v_t_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_x_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v_s_1672_; lean_object* v_t_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___x_1679_; uint8_t v_offsetCnstrs_1680_; 
v___x_1679_ = l_Lean_Meta_Context_config(v_a_1626_);
v_offsetCnstrs_1680_ = lean_ctor_get_uint8(v___x_1679_, 8);
lean_dec_ref(v___x_1679_);
if (v_offsetCnstrs_1680_ == 0)
{
uint8_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_s_1624_);
v___x_1681_ = 2;
v___x_1682_ = lean_box(v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; 
lean_inc_ref(v_s_1624_);
v___x_1684_ = l_Lean_Meta_isOffset_x3f(v_s_1624_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
if (lean_obj_tag(v_a_1685_) == 0)
{
lean_object* v___x_1686_; 
lean_inc_ref(v_s_1624_);
v___x_1686_ = l_Lean_Meta_evalNat(v_s_1624_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1738_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1738_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1738_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
if (lean_obj_tag(v_a_1687_) == 0)
{
uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_s_1624_);
v___x_1691_ = 2;
v___x_1692_ = lean_box(v___x_1691_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1692_);
v___x_1694_ = v___x_1689_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
lean_object* v_val_1696_; lean_object* v___x_1697_; 
lean_del_object(v___x_1689_);
v_val_1696_ = lean_ctor_get(v_a_1687_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_a_1687_, 1);
lean_inc_ref(v_t_1625_);
v___x_1697_ = l_Lean_Meta_isOffset_x3f(v_t_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
if (lean_obj_tag(v_a_1698_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_evalNat(v_t_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1714_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
if (lean_obj_tag(v_a_1700_) == 0)
{
uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_dec(v_val_1696_);
lean_dec_ref(v_s_1624_);
v___x_1704_ = 2;
v___x_1705_ = lean_box(v___x_1704_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1705_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
else
{
lean_object* v_val_1709_; uint8_t v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___f_1713_; 
lean_del_object(v___x_1702_);
v_val_1709_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1700_, 1);
v___x_1710_ = lean_nat_dec_eq(v_val_1696_, v_val_1709_);
lean_dec(v_val_1709_);
lean_dec(v_val_1696_);
v___x_1711_ = l_Lean_Bool_toLBool(v___x_1710_);
v___x_1712_ = lean_box(v___x_1711_);
v___f_1713_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1713_, 0, v___x_1712_);
v_x_1632_ = v___f_1713_;
v___y_1633_ = v_a_1626_;
v___y_1634_ = v_a_1627_;
v___y_1635_ = v_a_1628_;
v___y_1636_ = v_a_1629_;
goto v___jp_1631_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_val_1696_);
lean_dec_ref(v_s_1624_);
v_a_1715_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1699_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1699_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v_val_1723_; lean_object* v_fst_1724_; lean_object* v_snd_1725_; uint8_t v___x_1726_; 
lean_dec_ref(v_t_1625_);
v_val_1723_ = lean_ctor_get(v_a_1698_, 0);
lean_inc(v_val_1723_);
lean_dec_ref_known(v_a_1698_, 1);
v_fst_1724_ = lean_ctor_get(v_val_1723_, 0);
lean_inc(v_fst_1724_);
v_snd_1725_ = lean_ctor_get(v_val_1723_, 1);
lean_inc(v_snd_1725_);
lean_dec(v_val_1723_);
v___x_1726_ = lean_nat_dec_le(v_snd_1725_, v_val_1696_);
if (v___x_1726_ == 0)
{
lean_object* v___f_1727_; 
lean_dec(v_snd_1725_);
lean_dec(v_fst_1724_);
lean_dec(v_val_1696_);
v___f_1727_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
v_x_1632_ = v___f_1727_;
v___y_1633_ = v_a_1626_;
v___y_1634_ = v_a_1627_;
v___y_1635_ = v_a_1628_;
v___y_1636_ = v_a_1629_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_nat_sub(v_val_1696_, v_snd_1725_);
lean_dec(v_snd_1725_);
lean_dec(v_val_1696_);
v___x_1729_ = l_Lean_mkNatLit(v___x_1728_);
v_s_1672_ = v___x_1729_;
v_t_1673_ = v_fst_1724_;
v___y_1674_ = v_a_1626_;
v___y_1675_ = v_a_1627_;
v___y_1676_ = v_a_1628_;
v___y_1677_ = v_a_1629_;
goto v___jp_1671_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_val_1696_);
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_s_1624_);
v_a_1730_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1697_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1697_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_s_1624_);
v_a_1739_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1686_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1686_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_val_1747_; lean_object* v_fst_1748_; lean_object* v_snd_1749_; lean_object* v___x_1750_; 
v_val_1747_ = lean_ctor_get(v_a_1685_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v_a_1685_, 1);
v_fst_1748_ = lean_ctor_get(v_val_1747_, 0);
lean_inc(v_fst_1748_);
v_snd_1749_ = lean_ctor_get(v_val_1747_, 1);
lean_inc(v_snd_1749_);
lean_dec(v_val_1747_);
lean_inc_ref(v_t_1625_);
v___x_1750_ = l_Lean_Meta_isOffset_x3f(v_t_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
if (lean_obj_tag(v_a_1751_) == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Meta_evalNat(v_t_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1767_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1767_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1767_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 0)
{
uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_dec_ref(v_s_1624_);
v___x_1757_ = 2;
v___x_1758_ = lean_box(v___x_1757_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
else
{
lean_object* v_val_1762_; uint8_t v___x_1763_; 
lean_del_object(v___x_1755_);
v_val_1762_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v_a_1753_, 1);
v___x_1763_ = lean_nat_dec_le(v_snd_1749_, v_val_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___f_1764_; 
lean_dec(v_val_1762_);
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
v___f_1764_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
v_x_1632_ = v___f_1764_;
v___y_1633_ = v_a_1626_;
v___y_1634_ = v_a_1627_;
v___y_1635_ = v_a_1628_;
v___y_1636_ = v_a_1629_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_nat_sub(v_val_1762_, v_snd_1749_);
lean_dec(v_snd_1749_);
lean_dec(v_val_1762_);
v___x_1766_ = l_Lean_mkNatLit(v___x_1765_);
v_s_1672_ = v_fst_1748_;
v_t_1673_ = v___x_1766_;
v___y_1674_ = v_a_1626_;
v___y_1675_ = v_a_1627_;
v___y_1676_ = v_a_1628_;
v___y_1677_ = v_a_1629_;
goto v___jp_1671_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_dec_ref(v_s_1624_);
v_a_1768_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1752_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1752_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_val_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; uint8_t v___x_1779_; 
lean_dec_ref(v_t_1625_);
v_val_1776_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_val_1776_);
lean_dec_ref_known(v_a_1751_, 1);
v_fst_1777_ = lean_ctor_get(v_val_1776_, 0);
lean_inc(v_fst_1777_);
v_snd_1778_ = lean_ctor_get(v_val_1776_, 1);
lean_inc(v_snd_1778_);
lean_dec(v_val_1776_);
v___x_1779_ = lean_nat_dec_eq(v_snd_1749_, v_snd_1778_);
if (v___x_1779_ == 0)
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_nat_dec_lt(v_snd_1749_, v_snd_1778_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_nat_sub(v_snd_1749_, v_snd_1778_);
lean_dec(v_snd_1778_);
lean_dec(v_snd_1749_);
v___x_1782_ = l_Lean_Meta_mkOffset(v_fst_1748_, v___x_1781_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v_s_1672_ = v_a_1783_;
v_t_1673_ = v_fst_1777_;
v___y_1674_ = v_a_1626_;
v___y_1675_ = v_a_1627_;
v___y_1676_ = v_a_1628_;
v___y_1677_ = v_a_1629_;
goto v___jp_1671_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_fst_1777_);
lean_dec_ref(v_s_1624_);
v_a_1784_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1782_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_nat_sub(v_snd_1778_, v_snd_1749_);
lean_dec(v_snd_1749_);
lean_dec(v_snd_1778_);
v___x_1793_ = l_Lean_Meta_mkOffset(v_fst_1777_, v___x_1792_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v_s_1672_ = v_fst_1748_;
v_t_1673_ = v_a_1794_;
v___y_1674_ = v_a_1626_;
v___y_1675_ = v_a_1627_;
v___y_1676_ = v_a_1628_;
v___y_1677_ = v_a_1629_;
goto v___jp_1671_;
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_fst_1748_);
lean_dec_ref(v_s_1624_);
v_a_1795_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1793_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1793_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
else
{
lean_dec(v_snd_1778_);
lean_dec(v_snd_1749_);
v_s_1672_ = v_fst_1748_;
v_t_1673_ = v_fst_1777_;
v___y_1674_ = v_a_1626_;
v___y_1675_ = v_a_1627_;
v___y_1676_ = v_a_1628_;
v___y_1677_ = v_a_1629_;
goto v___jp_1671_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_s_1624_);
v_a_1803_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1750_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1750_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_s_1624_);
v_a_1811_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1684_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1684_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
v___jp_1631_:
{
lean_object* v___x_1637_; 
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
v___x_1637_ = lean_infer_type(v_s_1624_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = lean_obj_once(&l_Lean_Meta_isDefEqOffset___closed__1, &l_Lean_Meta_isDefEqOffset___closed__1_once, _init_l_Lean_Meta_isDefEqOffset___closed__1);
v___x_1640_ = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(v___x_1640_, 0, v_a_1638_);
lean_closure_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = 0;
v___x_1642_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___x_1640_, v___x_1641_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1654_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1654_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1654_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_unbox(v_a_1643_);
lean_dec(v_a_1643_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
lean_dec_ref(v_x_1632_);
v___x_1648_ = 2;
v___x_1649_ = lean_box(v___x_1648_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1649_);
v___x_1651_ = v___x_1645_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
else
{
lean_object* v___x_1653_; 
lean_del_object(v___x_1645_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
v___x_1653_ = lean_apply_5(v_x_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, lean_box(0));
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v_x_1632_);
v_a_1655_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1642_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1642_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec_ref(v_x_1632_);
v_a_1663_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1637_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1637_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
v___jp_1671_:
{
lean_object* v___f_1678_; 
v___f_1678_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1678_, 0, v_s_1672_);
lean_closure_set(v___f_1678_, 1, v_t_1673_);
v_x_1632_ = v___f_1678_;
v___y_1633_ = v___y_1674_;
v___y_1634_ = v___y_1675_;
v___y_1635_ = v___y_1676_;
v___y_1636_ = v___y_1677_;
goto v___jp_1631_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_isDefEqOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1624_ = stack[0].m_obj;
lean_object* v_t_1625_ = stack[1].m_obj;
lean_object* v_a_1626_ = stack[2].m_obj;
lean_object* v_a_1627_ = stack[3].m_obj;
lean_object* v_a_1628_ = stack[4].m_obj;
lean_object* v_a_1629_ = stack[5].m_obj;
lean_object* v_res_1819_;
v_res_1819_ = l_Lean_Meta_isDefEqOffset(v_s_1624_, v_t_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
stack->m_obj
 = v_res_1819_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object* v_s_1820_, lean_object* v_t_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_isDefEqOffset(v_s_1820_, v_t_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
return v_res_1827_;
}
}
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Offset(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Offset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Offset(builtin);
}
#ifdef __cplusplus
}
#endif
