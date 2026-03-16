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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0);
v___x_3_ = l_ReaderT_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object* v_e_10_, lean_object* v_k_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_toApplicative_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_126_; 
v___x_17_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
v_toApplicative_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_17_, 1);
lean_dec(v_unused_127_);
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_126_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_toApplicative_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_126_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v_toFunctor_22_; lean_object* v_toSeq_23_; lean_object* v_toSeqLeft_24_; lean_object* v_toSeqRight_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_124_; 
v_toFunctor_22_ = lean_ctor_get(v_toApplicative_18_, 0);
v_toSeq_23_ = lean_ctor_get(v_toApplicative_18_, 2);
v_toSeqLeft_24_ = lean_ctor_get(v_toApplicative_18_, 3);
v_toSeqRight_25_ = lean_ctor_get(v_toApplicative_18_, 4);
v_isSharedCheck_124_ = !lean_is_exclusive(v_toApplicative_18_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; 
v_unused_125_ = lean_ctor_get(v_toApplicative_18_, 1);
lean_dec(v_unused_125_);
v___x_27_ = v_toApplicative_18_;
v_isShared_28_ = v_isSharedCheck_124_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_toSeqRight_25_);
lean_inc(v_toSeqLeft_24_);
lean_inc(v_toSeq_23_);
lean_inc(v_toFunctor_22_);
lean_dec(v_toApplicative_18_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_124_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___f_34_; lean_object* v___f_35_; lean_object* v___f_36_; lean_object* v___x_38_; 
v___f_29_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
v___f_30_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref(v_toFunctor_22_);
v___f_31_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_31_, 0, v_toFunctor_22_);
v___f_32_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_32_, 0, v_toFunctor_22_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___f_31_);
lean_ctor_set(v___x_33_, 1, v___f_32_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_34_, 0, v_toSeqRight_25_);
v___f_35_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_35_, 0, v_toSeqLeft_24_);
v___f_36_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_36_, 0, v_toSeq_23_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 4, v___f_34_);
lean_ctor_set(v___x_27_, 3, v___f_35_);
lean_ctor_set(v___x_27_, 2, v___f_36_);
lean_ctor_set(v___x_27_, 1, v___f_29_);
lean_ctor_set(v___x_27_, 0, v___x_33_);
v___x_38_ = v___x_27_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___f_29_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v___f_36_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v___f_35_);
lean_ctor_set(v_reuseFailAlloc_123_, 4, v___f_34_);
v___x_38_ = v_reuseFailAlloc_123_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_40_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___f_30_);
lean_ctor_set(v___x_20_, 0, v___x_38_);
v___x_40_ = v___x_20_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___f_30_);
v___x_40_ = v_reuseFailAlloc_122_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v_toApplicative_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_120_; 
v___x_41_ = l_ReaderT_instMonad___redArg(v___x_40_);
v_toApplicative_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v___x_41_, 1);
lean_dec(v_unused_121_);
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_120_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_toApplicative_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_120_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v_toFunctor_46_; lean_object* v_toSeq_47_; lean_object* v_toSeqLeft_48_; lean_object* v_toSeqRight_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_118_; 
v_toFunctor_46_ = lean_ctor_get(v_toApplicative_42_, 0);
v_toSeq_47_ = lean_ctor_get(v_toApplicative_42_, 2);
v_toSeqLeft_48_ = lean_ctor_get(v_toApplicative_42_, 3);
v_toSeqRight_49_ = lean_ctor_get(v_toApplicative_42_, 4);
v_isSharedCheck_118_ = !lean_is_exclusive(v_toApplicative_42_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v_toApplicative_42_, 1);
lean_dec(v_unused_119_);
v___x_51_ = v_toApplicative_42_;
v_isShared_52_ = v_isSharedCheck_118_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_toSeqRight_49_);
lean_inc(v_toSeqLeft_48_);
lean_inc(v_toSeq_47_);
lean_inc(v_toFunctor_46_);
lean_dec(v_toApplicative_42_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_118_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___x_62_; 
v___f_53_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
v___f_54_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_46_);
v___f_55_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_55_, 0, v_toFunctor_46_);
v___f_56_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_56_, 0, v_toFunctor_46_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___f_55_);
lean_ctor_set(v___x_57_, 1, v___f_56_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_58_, 0, v_toSeqRight_49_);
v___f_59_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_59_, 0, v_toSeqLeft_48_);
v___f_60_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_60_, 0, v_toSeq_47_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 4, v___f_58_);
lean_ctor_set(v___x_51_, 3, v___f_59_);
lean_ctor_set(v___x_51_, 2, v___f_60_);
lean_ctor_set(v___x_51_, 1, v___f_53_);
lean_ctor_set(v___x_51_, 0, v___x_57_);
v___x_62_ = v___x_51_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___f_53_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v___f_60_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v___f_59_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___f_58_);
v___x_62_ = v_reuseFailAlloc_117_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_64_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___f_54_);
lean_ctor_set(v___x_44_, 0, v___x_62_);
v___x_64_ = v___x_44_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___f_54_);
v___x_64_ = v_reuseFailAlloc_116_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___f_65_; lean_object* v___f_66_; lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_getMCtx_76_; lean_object* v_modifyMCtx_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_115_; 
lean_inc_ref(v___x_64_);
v___f_65_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_65_, 0, v___x_64_);
lean_inc_ref(v___x_64_);
v___f_66_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_66_, 0, v___x_64_);
lean_inc_ref(v___x_64_);
v___f_67_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_67_, 0, v___x_64_);
lean_inc_ref(v___x_64_);
v___f_68_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_68_, 0, v___x_64_);
lean_inc_ref(v___x_64_);
v___f_69_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_69_, 0, v___x_64_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___f_65_);
lean_ctor_set(v___x_70_, 1, v___f_66_);
lean_inc_ref(v___x_64_);
v___x_71_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, v___x_64_);
v___x_72_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_ctor_set(v___x_72_, 2, v___f_67_);
lean_ctor_set(v___x_72_, 3, v___f_68_);
lean_ctor_set(v___x_72_, 4, v___f_69_);
lean_inc_ref(v___x_64_);
v___x_73_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_73_, 0, lean_box(0));
lean_closure_set(v___x_73_, 1, v___x_64_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_76_ = lean_ctor_get(v___x_75_, 0);
v_modifyMCtx_77_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_115_ == 0)
{
v___x_79_ = v___x_75_;
v_isShared_80_ = v_isSharedCheck_115_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_modifyMCtx_77_);
lean_inc(v_getMCtx_76_);
lean_dec(v___x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_115_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_81_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_81_, 0, lean_box(0));
lean_closure_set(v___x_81_, 1, v___x_64_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_82_, 0, v_modifyMCtx_77_);
lean_closure_set(v___f_82_, 1, v___x_81_);
v___f_83_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
v___x_84_ = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(v___x_84_, 0, lean_box(0));
lean_closure_set(v___x_84_, 1, lean_box(0));
lean_closure_set(v___x_84_, 2, v_getMCtx_76_);
lean_closure_set(v___x_84_, 3, v___f_83_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v___f_82_);
lean_ctor_set(v___x_79_, 0, v___x_84_);
v___x_86_ = v___x_79_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___f_82_);
v___x_86_ = v_reuseFailAlloc_114_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_388__overap_87_; lean_object* v___x_88_; 
v___x_388__overap_87_ = l_Lean_instantiateMVars___redArg(v___x_74_, v___x_86_, v_e_10_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
v___x_88_ = lean_apply_5(v___x_388__overap_87_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, lean_box(0));
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_105_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_105_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_105_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_105_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
if (lean_obj_tag(v_a_89_) == 0)
{
lean_object* v___x_93_; lean_object* v___x_95_; 
lean_dec(v_a_15_);
lean_dec_ref(v_a_14_);
lean_dec(v_a_13_);
lean_dec_ref(v_a_12_);
lean_dec_ref(v_k_11_);
v___x_93_ = lean_box(0);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v_val_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_val_97_ = lean_ctor_get(v_a_89_, 0);
lean_inc(v_val_97_);
lean_dec_ref(v_a_89_);
v___x_98_ = l_Lean_Expr_getAppFn(v_val_97_);
v___x_99_ = l_Lean_Expr_isMVar(v___x_98_);
lean_dec_ref(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_del_object(v___x_91_);
v___x_100_ = lean_apply_6(v_k_11_, v_val_97_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, lean_box(0));
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_103_; 
lean_dec(v_val_97_);
lean_dec(v_a_15_);
lean_dec_ref(v_a_14_);
lean_dec(v_a_13_);
lean_dec_ref(v_a_12_);
lean_dec_ref(v_k_11_);
v___x_101_ = lean_box(0);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_101_);
v___x_103_ = v___x_91_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
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
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_a_15_);
lean_dec_ref(v_a_14_);
lean_dec(v_a_13_);
lean_dec_ref(v_a_12_);
lean_dec_ref(v_k_11_);
v_a_106_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_88_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_88_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___boxed(lean_object* v_e_128_, lean_object* v_k_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(v_e_128_, v_k_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* v_00_u03b1_136_, lean_object* v_e_137_, lean_object* v_k_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; lean_object* v_toApplicative_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_253_; 
v___x_144_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
v_toApplicative_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v___x_144_, 1);
lean_dec(v_unused_254_);
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_253_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_toApplicative_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_253_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_toFunctor_149_; lean_object* v_toSeq_150_; lean_object* v_toSeqLeft_151_; lean_object* v_toSeqRight_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_251_; 
v_toFunctor_149_ = lean_ctor_get(v_toApplicative_145_, 0);
v_toSeq_150_ = lean_ctor_get(v_toApplicative_145_, 2);
v_toSeqLeft_151_ = lean_ctor_get(v_toApplicative_145_, 3);
v_toSeqRight_152_ = lean_ctor_get(v_toApplicative_145_, 4);
v_isSharedCheck_251_ = !lean_is_exclusive(v_toApplicative_145_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_toApplicative_145_, 1);
lean_dec(v_unused_252_);
v___x_154_ = v_toApplicative_145_;
v_isShared_155_ = v_isSharedCheck_251_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_toSeqRight_152_);
lean_inc(v_toSeqLeft_151_);
lean_inc(v_toSeq_150_);
lean_inc(v_toFunctor_149_);
lean_dec(v_toApplicative_145_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_251_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_165_; 
v___f_156_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
v___f_157_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref(v_toFunctor_149_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_149_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_159_, 0, v_toFunctor_149_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___f_158_);
lean_ctor_set(v___x_160_, 1, v___f_159_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqRight_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeqLeft_151_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_163_, 0, v_toSeq_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 4, v___f_161_);
lean_ctor_set(v___x_154_, 3, v___f_162_);
lean_ctor_set(v___x_154_, 2, v___f_163_);
lean_ctor_set(v___x_154_, 1, v___f_156_);
lean_ctor_set(v___x_154_, 0, v___x_160_);
v___x_165_ = v___x_154_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___f_156_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v___f_163_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v___f_162_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v___f_161_);
v___x_165_ = v_reuseFailAlloc_250_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___f_157_);
lean_ctor_set(v___x_147_, 0, v___x_165_);
v___x_167_ = v___x_147_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___f_157_);
v___x_167_ = v_reuseFailAlloc_249_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v_toApplicative_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_247_; 
v___x_168_ = l_ReaderT_instMonad___redArg(v___x_167_);
v_toApplicative_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v___x_168_, 1);
lean_dec(v_unused_248_);
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_247_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_toApplicative_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_247_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_toFunctor_173_; lean_object* v_toSeq_174_; lean_object* v_toSeqLeft_175_; lean_object* v_toSeqRight_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_245_; 
v_toFunctor_173_ = lean_ctor_get(v_toApplicative_169_, 0);
v_toSeq_174_ = lean_ctor_get(v_toApplicative_169_, 2);
v_toSeqLeft_175_ = lean_ctor_get(v_toApplicative_169_, 3);
v_toSeqRight_176_ = lean_ctor_get(v_toApplicative_169_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v_toApplicative_169_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_dec(v_unused_246_);
v___x_178_ = v_toApplicative_169_;
v_isShared_179_ = v_isSharedCheck_245_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toSeqRight_176_);
lean_inc(v_toSeqLeft_175_);
lean_inc(v_toSeq_174_);
lean_inc(v_toFunctor_173_);
lean_dec(v_toApplicative_169_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_245_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___x_189_; 
v___f_180_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
v___f_181_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_173_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_182_, 0, v_toFunctor_173_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_183_, 0, v_toFunctor_173_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___f_182_);
lean_ctor_set(v___x_184_, 1, v___f_183_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_185_, 0, v_toSeqRight_176_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_186_, 0, v_toSeqLeft_175_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_187_, 0, v_toSeq_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___f_185_);
lean_ctor_set(v___x_178_, 3, v___f_186_);
lean_ctor_set(v___x_178_, 2, v___f_187_);
lean_ctor_set(v___x_178_, 1, v___f_180_);
lean_ctor_set(v___x_178_, 0, v___x_184_);
v___x_189_ = v___x_178_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___f_180_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___f_187_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v___f_186_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v___f_185_);
v___x_189_ = v_reuseFailAlloc_244_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___f_181_);
lean_ctor_set(v___x_171_, 0, v___x_189_);
v___x_191_ = v___x_171_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___f_181_);
v___x_191_ = v_reuseFailAlloc_243_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_getMCtx_203_; lean_object* v_modifyMCtx_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_242_; 
lean_inc_ref(v___x_191_);
v___f_192_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_192_, 0, v___x_191_);
lean_inc_ref(v___x_191_);
v___f_193_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_193_, 0, v___x_191_);
lean_inc_ref(v___x_191_);
v___f_194_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_194_, 0, v___x_191_);
lean_inc_ref(v___x_191_);
v___f_195_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_195_, 0, v___x_191_);
lean_inc_ref(v___x_191_);
v___f_196_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_196_, 0, v___x_191_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___f_192_);
lean_ctor_set(v___x_197_, 1, v___f_193_);
lean_inc_ref(v___x_191_);
v___x_198_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_198_, 0, lean_box(0));
lean_closure_set(v___x_198_, 1, v___x_191_);
v___x_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_ctor_set(v___x_199_, 2, v___f_194_);
lean_ctor_set(v___x_199_, 3, v___f_195_);
lean_ctor_set(v___x_199_, 4, v___f_196_);
lean_inc_ref(v___x_191_);
v___x_200_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, v___x_191_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_203_ = lean_ctor_get(v___x_202_, 0);
v_modifyMCtx_204_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_242_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_242_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_modifyMCtx_204_);
lean_inc(v_getMCtx_203_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_242_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_208_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_208_, 0, lean_box(0));
lean_closure_set(v___x_208_, 1, v___x_191_);
v___f_209_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_209_, 0, v_modifyMCtx_204_);
lean_closure_set(v___f_209_, 1, v___x_208_);
v___f_210_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
v___x_211_ = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(v___x_211_, 0, lean_box(0));
lean_closure_set(v___x_211_, 1, lean_box(0));
lean_closure_set(v___x_211_, 2, v_getMCtx_203_);
lean_closure_set(v___x_211_, 3, v___f_210_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___f_209_);
lean_ctor_set(v___x_206_, 0, v___x_211_);
v___x_213_ = v___x_206_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___f_209_);
v___x_213_ = v_reuseFailAlloc_241_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_498__overap_214_; lean_object* v___x_215_; 
v___x_498__overap_214_ = l_Lean_instantiateMVars___redArg(v___x_201_, v___x_213_, v_e_137_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
v___x_215_ = lean_apply_5(v___x_498__overap_214_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_232_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_232_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_232_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_232_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
if (lean_obj_tag(v_a_216_) == 0)
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_k_138_);
v___x_220_ = lean_box(0);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
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
else
{
lean_object* v_val_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_val_224_ = lean_ctor_get(v_a_216_, 0);
lean_inc(v_val_224_);
lean_dec_ref(v_a_216_);
v___x_225_ = l_Lean_Expr_getAppFn(v_val_224_);
v___x_226_ = l_Lean_Expr_isMVar(v___x_225_);
lean_dec_ref(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_del_object(v___x_218_);
v___x_227_ = lean_apply_6(v_k_138_, v_val_224_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, lean_box(0));
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec(v_val_224_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_k_138_);
v___x_228_ = lean_box(0);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_228_);
v___x_230_ = v___x_218_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
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
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_k_138_);
v_a_233_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_215_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_215_);
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
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___boxed(lean_object* v_00_u03b1_255_, lean_object* v_e_256_, lean_object* v_k_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(v_00_u03b1_255_, v_e_256_, v_k_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_359_, v_a_361_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_1054_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_1054_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_1054_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = l_Lean_Expr_cleanupAnnotations(v_a_366_);
v___x_376_ = l_Lean_Expr_isApp(v___x_375_);
if (v___x_376_ == 0)
{
lean_dec_ref(v___x_375_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v_arg_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_arg_377_ = lean_ctor_get(v___x_375_, 1);
lean_inc_ref(v_arg_377_);
v___x_378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_375_);
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
v___x_380_ = l_Lean_Expr_isConstOf(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = l_Lean_Expr_isApp(v___x_378_);
if (v___x_381_ == 0)
{
lean_dec_ref(v___x_378_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v_arg_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_arg_382_ = lean_ctor_get(v___x_378_, 1);
lean_inc_ref(v_arg_382_);
v___x_383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_378_);
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3));
v___x_385_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5));
v___x_387_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7));
v___x_389_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9));
v___x_391_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11));
v___x_393_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
v___x_395_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_394_);
if (v___x_395_ == 0)
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Expr_isApp(v___x_383_);
if (v___x_396_ == 0)
{
lean_dec_ref(v___x_383_);
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v_arg_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_arg_397_ = lean_ctor_get(v___x_383_, 1);
lean_inc_ref(v_arg_397_);
v___x_398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_383_);
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16));
v___x_400_ = l_Lean_Expr_isConstOf(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; 
v___x_401_ = l_Lean_Expr_isApp(v___x_398_);
if (v___x_401_ == 0)
{
lean_dec_ref(v___x_398_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_398_);
v___x_403_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18));
v___x_404_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20));
v___x_406_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22));
v___x_408_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24));
v___x_410_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26));
v___x_412_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
v___x_414_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_413_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = l_Lean_Expr_isApp(v___x_402_);
if (v___x_415_ == 0)
{
lean_dec_ref(v___x_402_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_402_);
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30));
v___x_418_ = l_Lean_Expr_isConstOf(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_Expr_isApp(v___x_416_);
if (v___x_419_ == 0)
{
lean_dec_ref(v___x_416_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = l_Lean_Expr_appFnCleanup___redArg(v___x_416_);
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33));
v___x_422_ = l_Lean_Expr_isConstOf(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36));
v___x_424_ = l_Lean_Expr_isConstOf(v___x_420_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39));
v___x_426_ = l_Lean_Expr_isConstOf(v___x_420_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42));
v___x_428_ = l_Lean_Expr_isConstOf(v___x_420_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45));
v___x_430_ = l_Lean_Expr_isConstOf(v___x_420_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
v___x_432_ = l_Lean_Expr_isConstOf(v___x_420_, v___x_431_);
lean_dec_ref(v___x_420_);
if (v___x_432_ == 0)
{
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
goto v___jp_370_;
}
else
{
lean_object* v___x_433_; 
lean_del_object(v___x_368_);
v___x_433_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_465_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_465_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_465_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_465_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
uint8_t v___x_438_; 
v___x_438_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_439_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_443_; 
lean_del_object(v___x_436_);
lean_inc_ref(v_a_362_);
v___x_443_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
if (lean_obj_tag(v_a_444_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_443_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_446_; 
lean_dec_ref(v___x_443_);
v_val_445_ = lean_ctor_get(v_a_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref(v_a_444_);
v___x_446_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
if (lean_obj_tag(v_a_447_) == 0)
{
lean_dec(v_val_445_);
return v___x_446_;
}
else
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v___x_446_, 0);
lean_dec(v_unused_464_);
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
else
{
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_val_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_462_; 
v_val_451_ = lean_ctor_get(v_a_447_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_462_ == 0)
{
v___x_453_ = v_a_447_;
v_isShared_454_ = v_isSharedCheck_462_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_val_451_);
lean_dec(v_a_447_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_462_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_nat_add(v_val_445_, v_val_451_);
lean_dec(v_val_451_);
lean_dec(v_val_445_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_457_);
v___x_459_ = v___x_449_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
else
{
lean_dec(v_val_445_);
return v___x_446_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_466_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_433_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_433_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v___x_474_; 
lean_dec_ref(v___x_420_);
lean_del_object(v___x_368_);
v___x_474_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_506_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_506_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_506_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_506_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
uint8_t v___x_479_; 
v___x_479_ = lean_unbox(v_a_475_);
lean_dec(v_a_475_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_480_ = lean_box(0);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_480_);
v___x_482_ = v___x_477_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
else
{
lean_object* v___x_484_; 
lean_del_object(v___x_477_);
lean_inc_ref(v_a_362_);
v___x_484_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
if (lean_obj_tag(v_a_485_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_484_;
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; 
lean_dec_ref(v___x_484_);
v_val_486_ = lean_ctor_get(v_a_485_, 0);
lean_inc(v_val_486_);
lean_dec_ref(v_a_485_);
v___x_487_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
if (lean_obj_tag(v_a_488_) == 0)
{
lean_dec(v_val_486_);
return v___x_487_;
}
else
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_504_; 
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_487_, 0);
lean_dec(v_unused_505_);
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_504_;
goto v_resetjp_489_;
}
else
{
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_504_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_val_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_503_; 
v_val_492_ = lean_ctor_get(v_a_488_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_503_ == 0)
{
v___x_494_ = v_a_488_;
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_val_492_);
lean_dec(v_a_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_nat_sub(v_val_486_, v_val_492_);
lean_dec(v_val_492_);
lean_dec(v_val_486_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_498_);
v___x_500_ = v___x_490_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
else
{
lean_dec(v_val_486_);
return v___x_487_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_507_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_474_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_474_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref(v___x_420_);
lean_del_object(v___x_368_);
v___x_515_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_547_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_547_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_547_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_547_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
uint8_t v___x_520_; 
v___x_520_ = lean_unbox(v_a_516_);
lean_dec(v_a_516_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_521_ = lean_box(0);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_521_);
v___x_523_ = v___x_518_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_525_; 
lean_del_object(v___x_518_);
lean_inc_ref(v_a_362_);
v___x_525_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
if (lean_obj_tag(v_a_526_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_525_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_528_; 
lean_dec_ref(v___x_525_);
v_val_527_ = lean_ctor_get(v_a_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref(v_a_526_);
v___x_528_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
if (lean_obj_tag(v_a_529_) == 0)
{
lean_dec(v_val_527_);
return v___x_528_;
}
else
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_545_; 
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v___x_528_, 0);
lean_dec(v_unused_546_);
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_545_;
goto v_resetjp_530_;
}
else
{
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_545_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_val_533_ = lean_ctor_get(v_a_529_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v_a_529_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_a_529_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_nat_mul(v_val_527_, v_val_533_);
lean_dec(v_val_533_);
lean_dec(v_val_527_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_539_);
v___x_541_ = v___x_531_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
else
{
lean_dec(v_val_527_);
return v___x_528_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_525_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_548_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_515_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_515_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v___x_556_; 
lean_dec_ref(v___x_420_);
lean_del_object(v___x_368_);
v___x_556_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_588_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_588_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_588_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_588_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___x_561_; 
v___x_561_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_562_ = lean_box(0);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_562_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v___x_566_; 
lean_del_object(v___x_559_);
lean_inc_ref(v_a_362_);
v___x_566_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
if (lean_obj_tag(v_a_567_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_566_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; 
lean_dec_ref(v___x_566_);
v_val_568_ = lean_ctor_get(v_a_567_, 0);
lean_inc(v_val_568_);
lean_dec_ref(v_a_567_);
v___x_569_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
if (lean_obj_tag(v_a_570_) == 0)
{
lean_dec(v_val_568_);
return v___x_569_;
}
else
{
lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_586_; 
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v___x_569_, 0);
lean_dec(v_unused_587_);
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_586_;
goto v_resetjp_571_;
}
else
{
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_586_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_val_574_ = lean_ctor_get(v_a_570_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_a_570_);
if (v_isSharedCheck_585_ == 0)
{
v___x_576_ = v_a_570_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_dec(v_a_570_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_nat_div(v_val_568_, v_val_574_);
lean_dec(v_val_574_);
lean_dec(v_val_568_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_584_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_580_);
v___x_582_ = v___x_572_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
else
{
lean_dec(v_val_568_);
return v___x_569_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_589_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_556_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_556_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
else
{
lean_object* v___x_597_; 
lean_dec_ref(v___x_420_);
lean_del_object(v___x_368_);
v___x_597_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_629_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_629_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_629_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_629_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; 
v___x_602_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_603_ = lean_box(0);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
else
{
lean_object* v___x_607_; 
lean_del_object(v___x_600_);
lean_inc_ref(v_a_362_);
v___x_607_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
if (lean_obj_tag(v_a_608_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_607_;
}
else
{
lean_object* v_val_609_; lean_object* v___x_610_; 
lean_dec_ref(v___x_607_);
v_val_609_ = lean_ctor_get(v_a_608_, 0);
lean_inc(v_val_609_);
lean_dec_ref(v_a_608_);
v___x_610_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
if (lean_obj_tag(v_a_611_) == 0)
{
lean_dec(v_val_609_);
return v___x_610_;
}
else
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_610_, 0);
lean_dec(v_unused_628_);
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_627_;
goto v_resetjp_612_;
}
else
{
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_627_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_626_; 
v_val_615_ = lean_ctor_get(v_a_611_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_a_611_);
if (v_isSharedCheck_626_ == 0)
{
v___x_617_ = v_a_611_;
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_dec(v_a_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_nat_mod(v_val_609_, v_val_615_);
lean_dec(v_val_615_);
lean_dec(v_val_609_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_619_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_621_);
v___x_623_ = v___x_613_;
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
}
}
}
}
else
{
lean_dec(v_val_609_);
return v___x_610_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_630_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_597_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_597_);
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
lean_object* v___x_638_; 
lean_dec_ref(v___x_420_);
lean_del_object(v___x_368_);
v___x_638_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_649_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_649_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
uint8_t v___x_643_; 
v___x_643_ = lean_unbox(v_a_639_);
lean_dec(v_a_639_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_646_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_644_ = lean_box(0);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v___x_648_; 
lean_del_object(v___x_641_);
v___x_648_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_382_, v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_648_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_650_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_638_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_638_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
else
{
lean_object* v___x_658_; 
lean_dec_ref(v___x_416_);
lean_del_object(v___x_368_);
v___x_658_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_669_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint8_t v___x_663_; 
v___x_663_ = lean_unbox(v_a_659_);
lean_dec(v_a_659_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_664_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_664_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
lean_object* v___x_668_; 
lean_del_object(v___x_661_);
v___x_668_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_382_, v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_668_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_670_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_658_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_658_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v___x_402_);
lean_del_object(v___x_368_);
v___x_678_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_710_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_710_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_710_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_710_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
uint8_t v___x_683_; 
v___x_683_ = lean_unbox(v_a_679_);
lean_dec(v_a_679_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_684_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
else
{
lean_object* v___x_688_; 
lean_del_object(v___x_681_);
lean_inc_ref(v_a_362_);
v___x_688_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
if (lean_obj_tag(v_a_689_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_688_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_691_; 
lean_dec_ref(v___x_688_);
v_val_690_ = lean_ctor_get(v_a_689_, 0);
lean_inc(v_val_690_);
lean_dec_ref(v_a_689_);
v___x_691_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
if (lean_obj_tag(v_a_692_) == 0)
{
lean_dec(v_val_690_);
return v___x_691_;
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_708_; 
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_691_, 0);
lean_dec(v_unused_709_);
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
else
{
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_707_; 
v_val_696_ = lean_ctor_get(v_a_692_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_707_ == 0)
{
v___x_698_ = v_a_692_;
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v_a_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_nat_add(v_val_690_, v_val_696_);
lean_dec(v_val_696_);
lean_dec(v_val_690_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_702_);
v___x_704_ = v___x_694_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
else
{
lean_dec(v_val_690_);
return v___x_691_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_711_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_678_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_678_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_object* v___x_719_; 
lean_dec_ref(v___x_402_);
lean_del_object(v___x_368_);
v___x_719_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_751_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_751_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_751_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_751_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
uint8_t v___x_724_; 
v___x_724_ = lean_unbox(v_a_720_);
lean_dec(v_a_720_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_727_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_725_ = lean_box(0);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_729_; 
lean_del_object(v___x_722_);
lean_inc_ref(v_a_362_);
v___x_729_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
if (lean_obj_tag(v_a_730_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_729_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_732_; 
lean_dec_ref(v___x_729_);
v_val_731_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref(v_a_730_);
v___x_732_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
if (lean_obj_tag(v_a_733_) == 0)
{
lean_dec(v_val_731_);
return v___x_732_;
}
else
{
lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_749_; 
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_732_, 0);
lean_dec(v_unused_750_);
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_749_;
goto v_resetjp_734_;
}
else
{
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_749_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_val_737_ = lean_ctor_get(v_a_733_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_733_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v_a_733_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v_a_733_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_nat_sub(v_val_731_, v_val_737_);
lean_dec(v_val_737_);
lean_dec(v_val_731_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_743_);
v___x_745_ = v___x_735_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
else
{
lean_dec(v_val_731_);
return v___x_732_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_752_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_719_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_719_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v___x_760_; 
lean_dec_ref(v___x_402_);
lean_del_object(v___x_368_);
v___x_760_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_792_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_792_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_792_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_792_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; 
v___x_765_ = lean_unbox(v_a_761_);
lean_dec(v_a_761_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_766_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v___x_770_; 
lean_del_object(v___x_763_);
lean_inc_ref(v_a_362_);
v___x_770_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
if (lean_obj_tag(v_a_771_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_770_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_773_; 
lean_dec_ref(v___x_770_);
v_val_772_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v_a_771_);
v___x_773_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
if (lean_obj_tag(v_a_774_) == 0)
{
lean_dec(v_val_772_);
return v___x_773_;
}
else
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_790_; 
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_791_);
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_790_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_790_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_val_778_ = lean_ctor_get(v_a_774_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_774_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v_a_774_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_a_774_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_nat_mul(v_val_772_, v_val_778_);
lean_dec(v_val_778_);
lean_dec(v_val_772_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_784_);
v___x_786_ = v___x_776_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
else
{
lean_dec(v_val_772_);
return v___x_773_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_793_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_760_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_760_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
else
{
lean_object* v___x_801_; 
lean_dec_ref(v___x_402_);
lean_del_object(v___x_368_);
v___x_801_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_833_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_833_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_833_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_833_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
uint8_t v___x_806_; 
v___x_806_ = lean_unbox(v_a_802_);
lean_dec(v_a_802_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_807_ = lean_box(0);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_807_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_811_; 
lean_del_object(v___x_804_);
lean_inc_ref(v_a_362_);
v___x_811_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
if (lean_obj_tag(v_a_812_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_811_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_814_; 
lean_dec_ref(v___x_811_);
v_val_813_ = lean_ctor_get(v_a_812_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v_a_812_);
v___x_814_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
if (lean_obj_tag(v_a_815_) == 0)
{
lean_dec(v_val_813_);
return v___x_814_;
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_831_; 
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___x_814_, 0);
lean_dec(v_unused_832_);
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_831_;
goto v_resetjp_816_;
}
else
{
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_831_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_830_; 
v_val_819_ = lean_ctor_get(v_a_815_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_815_);
if (v_isSharedCheck_830_ == 0)
{
v___x_821_ = v_a_815_;
v_isShared_822_ = v_isSharedCheck_830_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v_a_815_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_830_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_nat_div(v_val_813_, v_val_819_);
lean_dec(v_val_819_);
lean_dec(v_val_813_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_825_);
v___x_827_ = v___x_817_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
else
{
lean_dec(v_val_813_);
return v___x_814_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_834_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_801_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_801_);
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
lean_object* v___x_842_; 
lean_dec_ref(v___x_402_);
lean_del_object(v___x_368_);
v___x_842_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_874_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_874_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_874_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_874_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___x_847_; 
v___x_847_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_850_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_848_ = lean_box(0);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_850_ = v___x_845_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v___x_852_; 
lean_del_object(v___x_845_);
lean_inc_ref(v_a_362_);
v___x_852_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
if (lean_obj_tag(v_a_853_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_852_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_855_; 
lean_dec_ref(v___x_852_);
v_val_854_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_val_854_);
lean_dec_ref(v_a_853_);
v___x_855_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
if (lean_obj_tag(v_a_856_) == 0)
{
lean_dec(v_val_854_);
return v___x_855_;
}
else
{
lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_872_; 
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___x_855_, 0);
lean_dec(v_unused_873_);
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_872_;
goto v_resetjp_857_;
}
else
{
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_872_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_val_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v_val_860_ = lean_ctor_get(v_a_856_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_856_);
if (v_isSharedCheck_871_ == 0)
{
v___x_862_ = v_a_856_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_val_860_);
lean_dec(v_a_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_nat_mod(v_val_854_, v_val_860_);
lean_dec(v_val_860_);
lean_dec(v_val_854_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_866_);
v___x_868_ = v___x_858_;
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
}
}
}
}
else
{
lean_dec(v_val_854_);
return v___x_855_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_852_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_875_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_842_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_842_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v___x_402_);
lean_del_object(v___x_368_);
v___x_883_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_397_, v_a_361_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_894_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_894_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_894_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_894_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
uint8_t v___x_888_; 
v___x_888_ = lean_unbox(v_a_884_);
lean_dec(v_a_884_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v___x_889_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_889_);
v___x_891_ = v___x_886_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
lean_object* v___x_893_; 
lean_del_object(v___x_886_);
v___x_893_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_382_, v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_893_;
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
v_a_895_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_883_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_883_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v___x_398_);
lean_dec_ref(v_arg_397_);
lean_del_object(v___x_368_);
v___x_903_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_377_, v_a_361_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v___x_908_; 
v___x_908_ = lean_unbox(v_a_904_);
lean_dec(v_a_904_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_a_362_);
v___x_909_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_913_; 
lean_del_object(v___x_906_);
v___x_913_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_913_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_arg_382_);
lean_dec_ref(v_a_362_);
v_a_915_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_903_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_903_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec_ref(v___x_383_);
lean_del_object(v___x_368_);
lean_inc_ref(v_a_362_);
v___x_923_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
if (lean_obj_tag(v_a_924_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_923_;
}
else
{
lean_object* v_val_925_; lean_object* v___x_926_; 
lean_dec_ref(v___x_923_);
v_val_925_ = lean_ctor_get(v_a_924_, 0);
lean_inc(v_val_925_);
lean_dec_ref(v_a_924_);
v___x_926_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
if (lean_obj_tag(v_a_927_) == 0)
{
lean_dec(v_val_925_);
return v___x_926_;
}
else
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_944_);
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_943_;
goto v_resetjp_928_;
}
else
{
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_943_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_val_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_942_; 
v_val_931_ = lean_ctor_get(v_a_927_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_942_ == 0)
{
v___x_933_ = v_a_927_;
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_val_931_);
lean_dec(v_a_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_nat_add(v_val_925_, v_val_931_);
lean_dec(v_val_931_);
lean_dec(v_val_925_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_937_);
v___x_939_ = v___x_929_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
else
{
lean_dec(v_val_925_);
return v___x_926_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_923_;
}
}
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_383_);
lean_del_object(v___x_368_);
lean_inc_ref(v_a_362_);
v___x_945_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
if (lean_obj_tag(v_a_946_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_945_;
}
else
{
lean_object* v_val_947_; lean_object* v___x_948_; 
lean_dec_ref(v___x_945_);
v_val_947_ = lean_ctor_get(v_a_946_, 0);
lean_inc(v_val_947_);
lean_dec_ref(v_a_946_);
v___x_948_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
if (lean_obj_tag(v_a_949_) == 0)
{
lean_dec(v_val_947_);
return v___x_948_;
}
else
{
lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_965_; 
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v___x_948_, 0);
lean_dec(v_unused_966_);
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_965_;
goto v_resetjp_950_;
}
else
{
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_965_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_964_; 
v_val_953_ = lean_ctor_get(v_a_949_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_949_);
if (v_isSharedCheck_964_ == 0)
{
v___x_955_ = v_a_949_;
v_isShared_956_ = v_isSharedCheck_964_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v_a_949_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_964_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_nat_sub(v_val_947_, v_val_953_);
lean_dec(v_val_953_);
lean_dec(v_val_947_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_959_);
v___x_961_ = v___x_951_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
else
{
lean_dec(v_val_947_);
return v___x_948_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_945_;
}
}
}
else
{
lean_object* v___x_967_; 
lean_dec_ref(v___x_383_);
lean_del_object(v___x_368_);
lean_inc_ref(v_a_362_);
v___x_967_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
if (lean_obj_tag(v_a_968_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_967_;
}
else
{
lean_object* v_val_969_; lean_object* v___x_970_; 
lean_dec_ref(v___x_967_);
v_val_969_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_val_969_);
lean_dec_ref(v_a_968_);
v___x_970_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
if (lean_obj_tag(v_a_971_) == 0)
{
lean_dec(v_val_969_);
return v___x_970_;
}
else
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_987_; 
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; 
v_unused_988_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_988_);
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_987_;
goto v_resetjp_972_;
}
else
{
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_987_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_986_; 
v_val_975_ = lean_ctor_get(v_a_971_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_a_971_);
if (v_isSharedCheck_986_ == 0)
{
v___x_977_ = v_a_971_;
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v_a_971_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = lean_nat_mul(v_val_969_, v_val_975_);
lean_dec(v_val_975_);
lean_dec(v_val_969_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_979_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_981_);
v___x_983_ = v___x_973_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
else
{
lean_dec(v_val_969_);
return v___x_970_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_967_;
}
}
}
else
{
lean_object* v___x_989_; 
lean_dec_ref(v___x_383_);
lean_del_object(v___x_368_);
lean_inc_ref(v_a_362_);
v___x_989_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
if (lean_obj_tag(v_a_990_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_989_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; 
lean_dec_ref(v___x_989_);
v_val_991_ = lean_ctor_get(v_a_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref(v_a_990_);
v___x_992_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
if (lean_obj_tag(v_a_993_) == 0)
{
lean_dec(v_val_991_);
return v___x_992_;
}
else
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1010_);
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1009_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1009_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_val_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1008_; 
v_val_997_ = lean_ctor_get(v_a_993_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_999_ = v_a_993_;
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_val_997_);
lean_dec(v_a_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_nat_div(v_val_991_, v_val_997_);
lean_dec(v_val_997_);
lean_dec(v_val_991_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1003_ = v___x_999_;
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
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1003_);
v___x_1005_ = v___x_995_;
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
lean_dec(v_val_991_);
return v___x_992_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_989_;
}
}
}
else
{
lean_object* v___x_1011_; 
lean_dec_ref(v___x_383_);
lean_del_object(v___x_368_);
lean_inc_ref(v_a_362_);
v___x_1011_ = l_Lean_Meta_evalNat(v_arg_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
if (lean_obj_tag(v_a_1012_) == 0)
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_1011_;
}
else
{
lean_object* v_val_1013_; lean_object* v___x_1014_; 
lean_dec_ref(v___x_1011_);
v_val_1013_ = lean_ctor_get(v_a_1012_, 0);
lean_inc(v_val_1013_);
lean_dec_ref(v_a_1012_);
v___x_1014_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
if (lean_obj_tag(v_a_1015_) == 0)
{
lean_dec(v_val_1013_);
return v___x_1014_;
}
else
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1031_; 
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_1014_, 0);
lean_dec(v_unused_1032_);
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1031_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1031_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_val_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1030_; 
v_val_1019_ = lean_ctor_get(v_a_1015_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_1015_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1021_ = v_a_1015_;
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_val_1019_);
lean_dec(v_a_1015_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_nat_mod(v_val_1013_, v_val_1019_);
lean_dec(v_val_1019_);
lean_dec(v_val_1013_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1025_);
v___x_1027_ = v___x_1017_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1013_);
return v___x_1014_;
}
}
}
else
{
lean_dec_ref(v_arg_377_);
lean_dec_ref(v_a_362_);
return v___x_1011_;
}
}
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v___x_383_);
lean_del_object(v___x_368_);
v___x_1033_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_382_, v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_1033_;
}
}
}
else
{
lean_object* v___x_1034_; 
lean_dec_ref(v___x_378_);
lean_del_object(v___x_368_);
v___x_1034_ = l_Lean_Meta_evalNat(v_arg_377_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
if (lean_obj_tag(v_a_1035_) == 0)
{
return v___x_1034_;
}
else
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1053_);
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1051_; 
v_val_1039_ = lean_ctor_get(v_a_1035_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1041_ = v_a_1035_;
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_a_1035_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_val_1039_, v___x_1043_);
lean_dec(v_val_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1044_);
v___x_1046_ = v___x_1041_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1046_);
v___x_1048_ = v___x_1037_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
else
{
return v___x_1034_;
}
}
}
v___jp_370_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_a_362_);
v_a_1055_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_365_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_365_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
switch(lean_obj_tag(v_e_1063_))
{
case 9:
{
lean_object* v_a_1072_; 
lean_dec_ref(v_a_1066_);
v_a_1072_ = lean_ctor_get(v_e_1063_, 0);
lean_inc_ref(v_a_1072_);
lean_dec_ref(v_e_1063_);
if (lean_obj_tag(v_a_1072_) == 0)
{
lean_object* v_val_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_val_1073_ = lean_ctor_get(v_a_1072_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_a_1072_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v_a_1072_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_val_1073_);
lean_dec(v_a_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_val_1073_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
else
{
lean_dec_ref(v_a_1072_);
goto v___jp_1069_;
}
}
case 10:
{
lean_object* v_expr_1082_; 
v_expr_1082_ = lean_ctor_get(v_e_1063_, 1);
lean_inc_ref(v_expr_1082_);
lean_dec_ref(v_e_1063_);
v_e_1063_ = v_expr_1082_;
goto _start;
}
case 4:
{
lean_object* v_declName_1084_; 
lean_dec_ref(v_a_1066_);
v_declName_1084_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_declName_1084_);
lean_dec_ref(v_e_1063_);
if (lean_obj_tag(v_declName_1084_) == 1)
{
lean_object* v_pre_1085_; 
v_pre_1085_ = lean_ctor_get(v_declName_1084_, 0);
lean_inc(v_pre_1085_);
if (lean_obj_tag(v_pre_1085_) == 1)
{
lean_object* v_pre_1086_; 
v_pre_1086_ = lean_ctor_get(v_pre_1085_, 0);
if (lean_obj_tag(v_pre_1086_) == 0)
{
lean_object* v_str_1087_; lean_object* v_str_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_str_1087_ = lean_ctor_get(v_declName_1084_, 1);
lean_inc_ref(v_str_1087_);
lean_dec_ref(v_declName_1084_);
v_str_1088_ = lean_ctor_get(v_pre_1085_, 1);
lean_inc_ref(v_str_1088_);
lean_dec_ref(v_pre_1085_);
v___x_1089_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__0));
v___x_1090_ = lean_string_dec_eq(v_str_1088_, v___x_1089_);
lean_dec_ref(v_str_1088_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_str_1087_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__1));
v___x_1092_ = lean_string_dec_eq(v_str_1087_, v___x_1091_);
lean_dec_ref(v_str_1087_);
if (v___x_1092_ == 0)
{
goto v___jp_1069_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__2));
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
}
else
{
lean_dec_ref(v_pre_1085_);
lean_dec_ref(v_declName_1084_);
goto v___jp_1069_;
}
}
else
{
lean_dec_ref(v_declName_1084_);
lean_dec(v_pre_1085_);
goto v___jp_1069_;
}
}
else
{
lean_dec(v_declName_1084_);
goto v___jp_1069_;
}
}
case 5:
{
lean_object* v___x_1095_; 
v___x_1095_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1095_;
}
case 2:
{
lean_object* v___x_1096_; 
v___x_1096_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1096_;
}
default: 
{
lean_dec_ref(v_a_1066_);
lean_dec_ref(v_e_1063_);
goto v___jp_1069_;
}
}
v___jp_1069_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(lean_object* v_b_1097_, lean_object* v_n_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1104_; 
lean_inc_ref(v_a_1101_);
v___x_1104_ = l_Lean_Meta_evalNat(v_n_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
if (lean_obj_tag(v_a_1105_) == 0)
{
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_b_1097_);
return v___x_1104_;
}
else
{
lean_object* v_val_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v___x_1104_);
v_val_1106_ = lean_ctor_get(v_a_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v_a_1105_);
v___x_1107_ = 1;
lean_inc_ref(v_a_1101_);
lean_inc(v_val_1106_);
v___x_1108_ = l_Lean_checkExponent(v_val_1106_, v___x_1107_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1137_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1137_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1137_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_unbox(v_a_1109_);
lean_dec(v_a_1109_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_dec(v_val_1106_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_b_1097_);
v___x_1114_ = lean_box(0);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
lean_object* v___x_1118_; 
lean_del_object(v___x_1111_);
v___x_1118_ = l_Lean_Meta_evalNat(v_b_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
if (lean_obj_tag(v_a_1119_) == 0)
{
lean_dec(v_val_1106_);
return v___x_1118_;
}
else
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1135_; 
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1136_);
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1135_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1135_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1134_; 
v_val_1123_ = lean_ctor_get(v_a_1119_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_a_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1125_ = v_a_1119_;
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v_a_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_nat_pow(v_val_1123_, v_val_1106_);
lean_dec(v_val_1106_);
lean_dec(v_val_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1129_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1106_);
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_val_1106_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_b_1097_);
v_a_1138_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1108_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1108_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_b_1097_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(lean_object* v_b_1146_, lean_object* v_n_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_b_1146_, v_n_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object* v_e_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Meta_evalNat(v_e_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(lean_object* v_k_1168_, uint8_t v_allowLevelAssignments_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1169_, v_k_1168_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_a_1184_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1175_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1175_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object* v_k_1192_, lean_object* v_allowLevelAssignments_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1199_; lean_object* v_res_1200_; 
v_allowLevelAssignments_boxed_1199_ = lean_unbox(v_allowLevelAssignments_1193_);
v_res_1200_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v_k_1192_, v_allowLevelAssignments_boxed_1199_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_object* v_00_u03b1_1201_, lean_object* v_k_1202_, uint8_t v_allowLevelAssignments_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v_k_1202_, v_allowLevelAssignments_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_k_1211_, lean_object* v_allowLevelAssignments_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1218_; lean_object* v_res_1219_; 
v_allowLevelAssignments_boxed_1218_ = lean_unbox(v_allowLevelAssignments_1212_);
v_res_1219_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(v_00_u03b1_1210_, v_k_1211_, v_allowLevelAssignments_boxed_1218_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t v___x_1220_, lean_object* v_e_1221_, lean_object* v_inst_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; uint8_t v_foApprox_1229_; uint8_t v_ctxApprox_1230_; uint8_t v_quasiPatternApprox_1231_; uint8_t v_constApprox_1232_; uint8_t v_isDefEqStuckEx_1233_; uint8_t v_unificationHints_1234_; uint8_t v_proofIrrelevance_1235_; uint8_t v_assignSyntheticOpaque_1236_; uint8_t v_offsetCnstrs_1237_; uint8_t v_etaStruct_1238_; uint8_t v_univApprox_1239_; uint8_t v_iota_1240_; uint8_t v_beta_1241_; uint8_t v_proj_1242_; uint8_t v_zeta_1243_; uint8_t v_zetaDelta_1244_; uint8_t v_zetaUnused_1245_; uint8_t v_zetaHave_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1285_; 
v___x_1228_ = l_Lean_Meta_Context_config(v___y_1223_);
v_foApprox_1229_ = lean_ctor_get_uint8(v___x_1228_, 0);
v_ctxApprox_1230_ = lean_ctor_get_uint8(v___x_1228_, 1);
v_quasiPatternApprox_1231_ = lean_ctor_get_uint8(v___x_1228_, 2);
v_constApprox_1232_ = lean_ctor_get_uint8(v___x_1228_, 3);
v_isDefEqStuckEx_1233_ = lean_ctor_get_uint8(v___x_1228_, 4);
v_unificationHints_1234_ = lean_ctor_get_uint8(v___x_1228_, 5);
v_proofIrrelevance_1235_ = lean_ctor_get_uint8(v___x_1228_, 6);
v_assignSyntheticOpaque_1236_ = lean_ctor_get_uint8(v___x_1228_, 7);
v_offsetCnstrs_1237_ = lean_ctor_get_uint8(v___x_1228_, 8);
v_etaStruct_1238_ = lean_ctor_get_uint8(v___x_1228_, 10);
v_univApprox_1239_ = lean_ctor_get_uint8(v___x_1228_, 11);
v_iota_1240_ = lean_ctor_get_uint8(v___x_1228_, 12);
v_beta_1241_ = lean_ctor_get_uint8(v___x_1228_, 13);
v_proj_1242_ = lean_ctor_get_uint8(v___x_1228_, 14);
v_zeta_1243_ = lean_ctor_get_uint8(v___x_1228_, 15);
v_zetaDelta_1244_ = lean_ctor_get_uint8(v___x_1228_, 16);
v_zetaUnused_1245_ = lean_ctor_get_uint8(v___x_1228_, 17);
v_zetaHave_1246_ = lean_ctor_get_uint8(v___x_1228_, 18);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1248_ = v___x_1228_;
v_isShared_1249_ = v_isSharedCheck_1285_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v___x_1228_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1285_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
uint8_t v_trackZetaDelta_1250_; lean_object* v_zetaDeltaSet_1251_; lean_object* v_lctx_1252_; lean_object* v_localInstances_1253_; lean_object* v_defEqCtx_x3f_1254_; lean_object* v_synthPendingDepth_1255_; lean_object* v_canUnfold_x3f_1256_; uint8_t v_univApprox_1257_; uint8_t v_inTypeClassResolution_1258_; uint8_t v_cacheInferType_1259_; lean_object* v_config_1261_; 
v_trackZetaDelta_1250_ = lean_ctor_get_uint8(v___y_1223_, sizeof(void*)*7);
v_zetaDeltaSet_1251_ = lean_ctor_get(v___y_1223_, 1);
lean_inc(v_zetaDeltaSet_1251_);
v_lctx_1252_ = lean_ctor_get(v___y_1223_, 2);
lean_inc_ref(v_lctx_1252_);
v_localInstances_1253_ = lean_ctor_get(v___y_1223_, 3);
lean_inc_ref(v_localInstances_1253_);
v_defEqCtx_x3f_1254_ = lean_ctor_get(v___y_1223_, 4);
lean_inc(v_defEqCtx_x3f_1254_);
v_synthPendingDepth_1255_ = lean_ctor_get(v___y_1223_, 5);
lean_inc(v_synthPendingDepth_1255_);
v_canUnfold_x3f_1256_ = lean_ctor_get(v___y_1223_, 6);
lean_inc(v_canUnfold_x3f_1256_);
v_univApprox_1257_ = lean_ctor_get_uint8(v___y_1223_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1258_ = lean_ctor_get_uint8(v___y_1223_, sizeof(void*)*7 + 2);
v_cacheInferType_1259_ = lean_ctor_get_uint8(v___y_1223_, sizeof(void*)*7 + 3);
if (v_isShared_1249_ == 0)
{
v_config_1261_ = v___x_1248_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 0, v_foApprox_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 1, v_ctxApprox_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 2, v_quasiPatternApprox_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 3, v_constApprox_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 4, v_isDefEqStuckEx_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 5, v_unificationHints_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 6, v_proofIrrelevance_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 7, v_assignSyntheticOpaque_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 8, v_offsetCnstrs_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 10, v_etaStruct_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 11, v_univApprox_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 12, v_iota_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 13, v_beta_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 14, v_proj_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 15, v_zeta_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 16, v_zetaDelta_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 17, v_zetaUnused_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 18, v_zetaHave_1246_);
v_config_1261_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
uint64_t v___x_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1276_; 
lean_ctor_set_uint8(v_config_1261_, 9, v___x_1220_);
v___x_1262_ = l_Lean_Meta_Context_configKey(v___y_1223_);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___y_1223_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; lean_object* v_unused_1278_; lean_object* v_unused_1279_; lean_object* v_unused_1280_; lean_object* v_unused_1281_; lean_object* v_unused_1282_; lean_object* v_unused_1283_; 
v_unused_1277_ = lean_ctor_get(v___y_1223_, 6);
lean_dec(v_unused_1277_);
v_unused_1278_ = lean_ctor_get(v___y_1223_, 5);
lean_dec(v_unused_1278_);
v_unused_1279_ = lean_ctor_get(v___y_1223_, 4);
lean_dec(v_unused_1279_);
v_unused_1280_ = lean_ctor_get(v___y_1223_, 3);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v___y_1223_, 2);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v___y_1223_, 1);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v___y_1223_, 0);
lean_dec(v_unused_1283_);
v___x_1264_ = v___y_1223_;
v_isShared_1265_ = v_isSharedCheck_1276_;
goto v_resetjp_1263_;
}
else
{
lean_dec(v___y_1223_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1276_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; uint64_t v_key_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1266_ = 2ULL;
v___x_1267_ = lean_uint64_shift_right(v___x_1262_, v___x_1266_);
v___x_1268_ = lean_uint64_shift_left(v___x_1267_, v___x_1266_);
v___x_1269_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1220_);
v_key_1270_ = lean_uint64_lor(v___x_1268_, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1271_, 0, v_config_1261_);
lean_ctor_set_uint64(v___x_1271_, sizeof(void*)*1, v_key_1270_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1271_);
v___x_1273_ = v___x_1264_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_zetaDeltaSet_1251_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_lctx_1252_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_localInstances_1253_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_defEqCtx_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1275_, 5, v_synthPendingDepth_1255_);
lean_ctor_set(v_reuseFailAlloc_1275_, 6, v_canUnfold_x3f_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, sizeof(void*)*7, v_trackZetaDelta_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, sizeof(void*)*7 + 1, v_univApprox_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, sizeof(void*)*7 + 3, v_cacheInferType_1259_);
v___x_1273_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_isExprDefEq(v_e_1221_, v_inst_1222_, v___x_1273_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object* v___x_1286_, lean_object* v_e_1287_, lean_object* v_inst_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v___x_746__boxed_1294_; lean_object* v_res_1295_; 
v___x_746__boxed_1294_ = lean_unbox(v___x_1286_);
v_res_1295_ = l_Lean_Meta_matchesInstance___lam__0(v___x_746__boxed_1294_, v_e_1287_, v_inst_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object* v_e_1296_, lean_object* v_inst_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___f_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1303_ = 3;
v___x_1304_ = lean_box(v___x_1303_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Meta_matchesInstance___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1305_, 0, v___x_1304_);
lean_closure_set(v___f_1305_, 1, v_e_1296_);
lean_closure_set(v___f_1305_, 2, v_inst_1297_);
v___x_1306_ = 0;
v___x_1307_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___f_1305_, v___x_1306_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___boxed(lean_object* v_e_1308_, lean_object* v_inst_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Meta_matchesInstance(v_e_1308_, v_inst_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1316_, v_a_1318_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1484_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1484_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1484_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = l_Lean_Expr_cleanupAnnotations(v_a_1323_);
v___x_1333_ = l_Lean_Expr_isApp(v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v___x_1332_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v_arg_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_arg_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc_ref(v_arg_1334_);
v___x_1335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1332_);
v___x_1336_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
v___x_1337_ = l_Lean_Expr_isConstOf(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
uint8_t v___x_1338_; 
v___x_1338_ = l_Lean_Expr_isApp(v___x_1335_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v_arg_1339_; lean_object* v_b_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_arg_1339_ = lean_ctor_get(v___x_1335_, 1);
lean_inc_ref(v_arg_1339_);
v___x_1399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1335_);
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
v___x_1401_ = l_Lean_Expr_isConstOf(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Lean_Expr_isApp(v___x_1399_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v___x_1399_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v_arg_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_arg_1403_ = lean_ctor_get(v___x_1399_, 1);
lean_inc_ref(v_arg_1403_);
v___x_1404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1399_);
v___x_1405_ = l_Lean_Expr_isApp(v___x_1404_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v___x_1404_);
lean_dec_ref(v_arg_1403_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1404_);
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
v___x_1408_ = l_Lean_Expr_isConstOf(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Lean_Expr_isApp(v___x_1406_);
if (v___x_1409_ == 0)
{
lean_dec_ref(v___x_1406_);
lean_dec_ref(v_arg_1403_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1406_);
v___x_1411_ = l_Lean_Expr_isApp(v___x_1410_);
if (v___x_1411_ == 0)
{
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_arg_1403_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1410_);
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
v___x_1414_ = l_Lean_Expr_isConstOf(v___x_1412_, v___x_1413_);
lean_dec_ref(v___x_1412_);
if (v___x_1414_ == 0)
{
lean_dec_ref(v_arg_1403_);
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_del_object(v___x_1325_);
v___x_1415_ = l_Lean_Nat_mkInstHAdd;
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc_ref(v_a_1317_);
v___x_1416_ = l_Lean_Meta_matchesInstance(v_arg_1403_, v___x_1415_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1426_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_unbox(v_a_1417_);
lean_dec(v_a_1417_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
v___x_1422_ = lean_box(0);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1422_);
v___x_1424_ = v___x_1419_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
lean_del_object(v___x_1419_);
v_b_1341_ = v_arg_1334_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
goto v___jp_1340_;
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
v_a_1427_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1416_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1416_);
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
}
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v___x_1406_);
lean_del_object(v___x_1325_);
v___x_1435_ = l_Lean_Nat_mkInstAdd;
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc_ref(v_a_1317_);
v___x_1436_ = l_Lean_Meta_matchesInstance(v_arg_1403_, v___x_1435_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_unbox(v_a_1437_);
lean_dec(v_a_1437_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
v___x_1442_ = lean_box(0);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1442_);
v___x_1444_ = v___x_1439_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
else
{
lean_del_object(v___x_1439_);
v_b_1341_ = v_arg_1334_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
goto v___jp_1340_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_arg_1339_);
lean_dec_ref(v_arg_1334_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
v_a_1447_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1436_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1436_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1399_);
lean_del_object(v___x_1325_);
v_b_1341_ = v_arg_1334_;
v___y_1342_ = v_a_1317_;
v___y_1343_ = v_a_1318_;
v___y_1344_ = v_a_1319_;
v___y_1345_ = v_a_1320_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v___x_1346_; 
lean_inc_ref(v___y_1344_);
v___x_1346_ = l_Lean_Meta_evalNat(v_b_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1390_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1390_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1390_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v_arg_1339_);
v___x_1351_ = lean_box(0);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v_val_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1389_; 
lean_del_object(v___x_1349_);
v_val_1355_ = lean_ctor_get(v_a_1347_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_a_1347_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1357_ = v_a_1347_;
v_isShared_1358_ = v_isSharedCheck_1389_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_val_1355_);
lean_dec(v_a_1347_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1389_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; 
v___x_1359_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_arg_1339_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1380_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1380_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1380_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_fst_1364_; lean_object* v_snd_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1379_; 
v_fst_1364_ = lean_ctor_get(v_a_1360_, 0);
v_snd_1365_ = lean_ctor_get(v_a_1360_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1367_ = v_a_1360_;
v_isShared_1368_ = v_isSharedCheck_1379_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1365_);
lean_inc(v_fst_1364_);
lean_dec(v_a_1360_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1379_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_nat_add(v_snd_1365_, v_val_1355_);
lean_dec(v_val_1355_);
lean_dec(v_snd_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_fst_1364_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1371_);
v___x_1373_ = v___x_1357_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1373_);
v___x_1375_ = v___x_1362_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
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
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_del_object(v___x_1357_);
lean_dec(v_val_1355_);
v_a_1381_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1359_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1359_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v_arg_1339_);
v_a_1391_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1346_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1346_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
else
{
lean_object* v___x_1455_; 
lean_dec_ref(v___x_1335_);
lean_del_object(v___x_1325_);
v___x_1455_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_arg_1334_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1475_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1475_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1475_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v_fst_1460_; lean_object* v_snd_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1474_; 
v_fst_1460_ = lean_ctor_get(v_a_1456_, 0);
v_snd_1461_ = lean_ctor_get(v_a_1456_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_a_1456_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1463_ = v_a_1456_;
v_isShared_1464_ = v_isSharedCheck_1474_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snd_1461_);
lean_inc(v_fst_1460_);
lean_dec(v_a_1456_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1474_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v_snd_1461_, v___x_1465_);
lean_dec(v_snd_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v___x_1466_);
v___x_1468_ = v___x_1463_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_fst_1460_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1469_);
v___x_1471_ = v___x_1458_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1455_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1455_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1328_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
v_a_1485_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1322_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1322_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* v_e_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; 
lean_inc_ref(v_e_1493_);
v___x_1499_ = l_Lean_Meta_isOffset_x3f(v_e_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1513_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1513_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1513_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
if (lean_obj_tag(v_a_1500_) == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_e_1493_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
else
{
lean_object* v_val_1509_; lean_object* v___x_1511_; 
lean_dec_ref(v_e_1493_);
v_val_1509_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_val_1509_);
lean_dec_ref(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_val_1509_);
v___x_1511_ = v___x_1502_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_val_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_e_1493_);
v_a_1514_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1499_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1499_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object* v_e_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_e_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f___boxed(lean_object* v_e_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Meta_isOffset_x3f(v_e_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* v_e_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_evalNat(v_e_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1559_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1559_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1559_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
if (lean_obj_tag(v_a_1543_) == 1)
{
lean_object* v_val_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v_val_1547_ = lean_ctor_get(v_a_1543_, 0);
lean_inc(v_val_1547_);
lean_dec_ref(v_a_1543_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_nat_dec_eq(v_val_1547_, v___x_1548_);
lean_dec(v_val_1547_);
v___x_1550_ = lean_box(v___x_1549_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1550_);
v___x_1552_ = v___x_1545_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
else
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_dec(v_a_1543_);
v___x_1554_ = 0;
v___x_1555_ = lean_box(v___x_1554_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1555_);
v___x_1557_ = v___x_1545_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1542_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1542_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object* v_e_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object* v_e_1575_, lean_object* v_offset_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = lean_nat_dec_eq(v_offset_1576_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_inc_ref(v_e_1575_);
v___x_1584_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1575_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1599_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1599_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1599_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_unbox(v_a_1585_);
lean_dec(v_a_1585_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = l_Lean_mkNatLit(v_offset_1576_);
v___x_1591_ = l_Lean_mkNatAdd(v_e_1575_, v___x_1590_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1591_);
v___x_1593_ = v___x_1587_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec_ref(v_e_1575_);
v___x_1595_ = l_Lean_mkNatLit(v_offset_1576_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1595_);
v___x_1597_ = v___x_1587_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_offset_1576_);
lean_dec_ref(v_e_1575_);
v_a_1600_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1584_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1584_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec_ref(v_a_1579_);
lean_dec(v_offset_1576_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_e_1575_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset___boxed(lean_object* v_e_1609_, lean_object* v_offset_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(v_e_1609_, v_offset_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object* v_s_1617_, lean_object* v_t_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_is_expr_def_eq(v_s_1617_, v_t_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1635_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint8_t v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1629_ = lean_unbox(v_a_1625_);
lean_dec(v_a_1625_);
v___x_1630_ = l_Bool_toLBool(v___x_1629_);
v___x_1631_ = lean_box(v___x_1630_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1631_);
v___x_1633_ = v___x_1627_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1624_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1624_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0___boxed(lean_object* v_s_1644_, lean_object* v_t_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_isDefEqOffset___lam__0(v_s_1644_, v_t_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(uint8_t v___x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_box(v___x_1652_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1___boxed(lean_object* v___x_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v___x_3826__boxed_1666_; lean_object* v_res_1667_; 
v___x_3826__boxed_1666_ = lean_unbox(v___x_1660_);
v_res_1667_ = l_Lean_Meta_isDefEqOffset___lam__1(v___x_3826__boxed_1666_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1667_;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___closed__1(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_box(0);
v___x_1671_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__0));
v___x_1672_ = l_Lean_mkConst(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object* v_s_1676_, lean_object* v_t_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_x_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v_s_1724_; lean_object* v_t_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_getConfig___redArg(v_a_1678_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1877_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1877_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1877_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
uint8_t v_offsetCnstrs_1736_; 
v_offsetCnstrs_1736_ = lean_ctor_get_uint8(v_a_1732_, 8);
lean_dec(v_a_1732_);
if (v_offsetCnstrs_1736_ == 0)
{
uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v___x_1737_ = 2;
v___x_1738_ = lean_box(v___x_1737_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1738_);
v___x_1740_ = v___x_1734_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
else
{
lean_object* v___x_1742_; 
lean_del_object(v___x_1734_);
lean_inc(v_a_1681_);
lean_inc_ref(v_a_1680_);
lean_inc(v_a_1679_);
lean_inc_ref(v_a_1678_);
lean_inc_ref(v_s_1676_);
v___x_1742_ = l_Lean_Meta_isOffset_x3f(v_s_1676_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1742_);
if (lean_obj_tag(v_a_1743_) == 0)
{
lean_object* v___x_1744_; 
lean_inc_ref(v_a_1680_);
lean_inc_ref(v_s_1676_);
v___x_1744_ = l_Lean_Meta_evalNat(v_s_1676_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1796_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1796_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1796_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
if (lean_obj_tag(v_a_1745_) == 0)
{
uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v___x_1749_ = 2;
v___x_1750_ = lean_box(v___x_1749_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1750_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
else
{
lean_object* v_val_1754_; lean_object* v___x_1755_; 
lean_del_object(v___x_1747_);
v_val_1754_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_val_1754_);
lean_dec_ref(v_a_1745_);
lean_inc(v_a_1681_);
lean_inc_ref(v_a_1680_);
lean_inc(v_a_1679_);
lean_inc_ref(v_a_1678_);
lean_inc_ref(v_t_1677_);
v___x_1755_ = l_Lean_Meta_isOffset_x3f(v_t_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
if (lean_obj_tag(v_a_1756_) == 0)
{
lean_object* v___x_1757_; 
lean_inc_ref(v_a_1680_);
v___x_1757_ = l_Lean_Meta_evalNat(v_t_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1772_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1772_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1772_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
if (lean_obj_tag(v_a_1758_) == 0)
{
uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec(v_val_1754_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_s_1676_);
v___x_1762_ = 2;
v___x_1763_ = lean_box(v___x_1762_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1763_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v_val_1767_; uint8_t v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; 
lean_del_object(v___x_1760_);
v_val_1767_ = lean_ctor_get(v_a_1758_, 0);
lean_inc(v_val_1767_);
lean_dec_ref(v_a_1758_);
v___x_1768_ = lean_nat_dec_eq(v_val_1754_, v_val_1767_);
lean_dec(v_val_1767_);
lean_dec(v_val_1754_);
v___x_1769_ = l_Bool_toLBool(v___x_1768_);
v___x_1770_ = lean_box(v___x_1769_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1771_, 0, v___x_1770_);
v_x_1684_ = v___f_1771_;
v___y_1685_ = v_a_1678_;
v___y_1686_ = v_a_1679_;
v___y_1687_ = v_a_1680_;
v___y_1688_ = v_a_1681_;
goto v___jp_1683_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_val_1754_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_s_1676_);
v_a_1773_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1757_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1757_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_val_1781_; lean_object* v_fst_1782_; lean_object* v_snd_1783_; uint8_t v___x_1784_; 
lean_dec_ref(v_t_1677_);
v_val_1781_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_val_1781_);
lean_dec_ref(v_a_1756_);
v_fst_1782_ = lean_ctor_get(v_val_1781_, 0);
lean_inc(v_fst_1782_);
v_snd_1783_ = lean_ctor_get(v_val_1781_, 1);
lean_inc(v_snd_1783_);
lean_dec(v_val_1781_);
v___x_1784_ = lean_nat_dec_le(v_snd_1783_, v_val_1754_);
if (v___x_1784_ == 0)
{
lean_object* v___f_1785_; 
lean_dec(v_snd_1783_);
lean_dec(v_fst_1782_);
lean_dec(v_val_1754_);
v___f_1785_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
v_x_1684_ = v___f_1785_;
v___y_1685_ = v_a_1678_;
v___y_1686_ = v_a_1679_;
v___y_1687_ = v_a_1680_;
v___y_1688_ = v_a_1681_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_nat_sub(v_val_1754_, v_snd_1783_);
lean_dec(v_snd_1783_);
lean_dec(v_val_1754_);
v___x_1787_ = l_Lean_mkNatLit(v___x_1786_);
v_s_1724_ = v___x_1787_;
v_t_1725_ = v_fst_1782_;
v___y_1726_ = v_a_1678_;
v___y_1727_ = v_a_1679_;
v___y_1728_ = v_a_1680_;
v___y_1729_ = v_a_1681_;
goto v___jp_1723_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_val_1754_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v_a_1788_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1755_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1755_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v_a_1797_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1744_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1744_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_val_1805_; lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1808_; 
v_val_1805_ = lean_ctor_get(v_a_1743_, 0);
lean_inc(v_val_1805_);
lean_dec_ref(v_a_1743_);
v_fst_1806_ = lean_ctor_get(v_val_1805_, 0);
lean_inc(v_fst_1806_);
v_snd_1807_ = lean_ctor_get(v_val_1805_, 1);
lean_inc(v_snd_1807_);
lean_dec(v_val_1805_);
lean_inc(v_a_1681_);
lean_inc_ref(v_a_1680_);
lean_inc(v_a_1679_);
lean_inc_ref(v_a_1678_);
lean_inc_ref(v_t_1677_);
v___x_1808_ = l_Lean_Meta_isOffset_x3f(v_t_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
if (lean_obj_tag(v_a_1809_) == 0)
{
lean_object* v___x_1810_; 
lean_inc_ref(v_a_1680_);
v___x_1810_ = l_Lean_Meta_evalNat(v_t_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1825_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1825_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1825_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
if (lean_obj_tag(v_a_1811_) == 0)
{
uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec(v_snd_1807_);
lean_dec(v_fst_1806_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_s_1676_);
v___x_1815_ = 2;
v___x_1816_ = lean_box(v___x_1815_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
lean_object* v_val_1820_; uint8_t v___x_1821_; 
lean_del_object(v___x_1813_);
v_val_1820_ = lean_ctor_get(v_a_1811_, 0);
lean_inc(v_val_1820_);
lean_dec_ref(v_a_1811_);
v___x_1821_ = lean_nat_dec_le(v_snd_1807_, v_val_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___f_1822_; 
lean_dec(v_val_1820_);
lean_dec(v_snd_1807_);
lean_dec(v_fst_1806_);
v___f_1822_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
v_x_1684_ = v___f_1822_;
v___y_1685_ = v_a_1678_;
v___y_1686_ = v_a_1679_;
v___y_1687_ = v_a_1680_;
v___y_1688_ = v_a_1681_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_nat_sub(v_val_1820_, v_snd_1807_);
lean_dec(v_snd_1807_);
lean_dec(v_val_1820_);
v___x_1824_ = l_Lean_mkNatLit(v___x_1823_);
v_s_1724_ = v_fst_1806_;
v_t_1725_ = v___x_1824_;
v___y_1726_ = v_a_1678_;
v___y_1727_ = v_a_1679_;
v___y_1728_ = v_a_1680_;
v___y_1729_ = v_a_1681_;
goto v___jp_1723_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_snd_1807_);
lean_dec(v_fst_1806_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_s_1676_);
v_a_1826_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1810_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1810_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_val_1834_; lean_object* v_fst_1835_; lean_object* v_snd_1836_; uint8_t v___x_1837_; 
lean_dec_ref(v_t_1677_);
v_val_1834_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_val_1834_);
lean_dec_ref(v_a_1809_);
v_fst_1835_ = lean_ctor_get(v_val_1834_, 0);
lean_inc(v_fst_1835_);
v_snd_1836_ = lean_ctor_get(v_val_1834_, 1);
lean_inc(v_snd_1836_);
lean_dec(v_val_1834_);
v___x_1837_ = lean_nat_dec_eq(v_snd_1807_, v_snd_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_nat_dec_lt(v_snd_1807_, v_snd_1836_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_nat_sub(v_snd_1807_, v_snd_1836_);
lean_dec(v_snd_1836_);
lean_dec(v_snd_1807_);
lean_inc_ref(v_a_1680_);
v___x_1840_ = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(v_fst_1806_, v___x_1839_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v_s_1724_ = v_a_1841_;
v_t_1725_ = v_fst_1835_;
v___y_1726_ = v_a_1678_;
v___y_1727_ = v_a_1679_;
v___y_1728_ = v_a_1680_;
v___y_1729_ = v_a_1681_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_fst_1835_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_s_1676_);
v_a_1842_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1840_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_nat_sub(v_snd_1836_, v_snd_1807_);
lean_dec(v_snd_1807_);
lean_dec(v_snd_1836_);
lean_inc_ref(v_a_1680_);
v___x_1851_ = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(v_fst_1835_, v___x_1850_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v_s_1724_ = v_fst_1806_;
v_t_1725_ = v_a_1852_;
v___y_1726_ = v_a_1678_;
v___y_1727_ = v_a_1679_;
v___y_1728_ = v_a_1680_;
v___y_1729_ = v_a_1681_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_fst_1806_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_s_1676_);
v_a_1853_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1851_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1851_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_dec(v_snd_1836_);
lean_dec(v_snd_1807_);
v_s_1724_ = v_fst_1806_;
v_t_1725_ = v_fst_1835_;
v___y_1726_ = v_a_1678_;
v___y_1727_ = v_a_1679_;
v___y_1728_ = v_a_1680_;
v___y_1729_ = v_a_1681_;
goto v___jp_1723_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_snd_1807_);
lean_dec(v_fst_1806_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v_a_1861_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1808_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1808_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v_a_1869_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1742_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1742_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_t_1677_);
lean_dec_ref(v_s_1676_);
v_a_1878_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1731_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1731_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
v___jp_1683_:
{
lean_object* v___x_1689_; 
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
v___x_1689_ = lean_infer_type(v_s_1676_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = lean_obj_once(&l_Lean_Meta_isDefEqOffset___closed__1, &l_Lean_Meta_isDefEqOffset___closed__1_once, _init_l_Lean_Meta_isDefEqOffset___closed__1);
v___x_1692_ = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(v___x_1692_, 0, v_a_1690_);
lean_closure_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = 0;
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
v___x_1694_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___x_1692_, v___x_1693_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_unbox(v_a_1695_);
lean_dec(v_a_1695_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v_x_1684_);
v___x_1700_ = 2;
v___x_1701_ = lean_box(v___x_1700_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1701_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; 
lean_del_object(v___x_1697_);
v___x_1705_ = lean_apply_5(v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, lean_box(0));
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v_x_1684_);
v_a_1707_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1694_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1694_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v_x_1684_);
v_a_1715_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1689_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1689_);
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
v___jp_1723_:
{
lean_object* v___f_1730_; 
v___f_1730_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1730_, 0, v_s_1724_);
lean_closure_set(v___f_1730_, 1, v_t_1725_);
v_x_1684_ = v___f_1730_;
v___y_1685_ = v___y_1726_;
v___y_1686_ = v___y_1727_;
v___y_1687_ = v___y_1728_;
v___y_1688_ = v___y_1729_;
goto v___jp_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object* v_s_1886_, lean_object* v_t_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Meta_isDefEqOffset(v_s_1886_, v_t_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v_res_1893_;
}
}
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
