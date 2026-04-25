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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
v___x_1_ = l_instMonadEIO(lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object* v_e_10_, lean_object* v_k_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
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
lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_getMCtx_68_; lean_object* v_modifyMCtx_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_384__overap_75_; lean_object* v___x_76_; 
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
v___x_384__overap_75_ = l_Lean_instantiateMVars___redArg(v___x_66_, v___x_74_, v_e_10_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
v___x_76_ = lean_apply_5(v___x_384__overap_75_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, lean_box(0));
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
lean_dec_ref(v_a_77_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___boxed(lean_object* v_e_108_, lean_object* v_k_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(v_e_108_, v_k_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* v_00_u03b1_116_, lean_object* v_e_117_, lean_object* v_k_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v_toApplicative_125_; lean_object* v_toFunctor_126_; lean_object* v_toSeq_127_; lean_object* v_toSeqLeft_128_; lean_object* v_toSeqRight_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_toApplicative_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_213_; 
v___x_124_ = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
v_toApplicative_125_ = lean_ctor_get(v___x_124_, 0);
v_toFunctor_126_ = lean_ctor_get(v_toApplicative_125_, 0);
v_toSeq_127_ = lean_ctor_get(v_toApplicative_125_, 2);
v_toSeqLeft_128_ = lean_ctor_get(v_toApplicative_125_, 3);
v_toSeqRight_129_ = lean_ctor_get(v_toApplicative_125_, 4);
v___f_130_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
v___f_131_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_126_, 2);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_132_, 0, v_toFunctor_126_);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_133_, 0, v_toFunctor_126_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___f_132_);
lean_ctor_set(v___x_134_, 1, v___f_133_);
lean_inc(v_toSeqRight_129_);
v___f_135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_135_, 0, v_toSeqRight_129_);
lean_inc(v_toSeqLeft_128_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeqLeft_128_);
lean_inc(v_toSeq_127_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_137_, 0, v_toSeq_127_);
v___x_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_138_, 0, v___x_134_);
lean_ctor_set(v___x_138_, 1, v___f_130_);
lean_ctor_set(v___x_138_, 2, v___f_137_);
lean_ctor_set(v___x_138_, 3, v___f_136_);
lean_ctor_set(v___x_138_, 4, v___f_135_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___f_131_);
v___x_140_ = l_StateRefT_x27_instMonad___redArg(v___x_139_);
v_toApplicative_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v___x_140_, 1);
lean_dec(v_unused_214_);
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_213_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_toApplicative_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_213_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_toFunctor_145_; lean_object* v_toSeq_146_; lean_object* v_toSeqLeft_147_; lean_object* v_toSeqRight_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_211_; 
v_toFunctor_145_ = lean_ctor_get(v_toApplicative_141_, 0);
v_toSeq_146_ = lean_ctor_get(v_toApplicative_141_, 2);
v_toSeqLeft_147_ = lean_ctor_get(v_toApplicative_141_, 3);
v_toSeqRight_148_ = lean_ctor_get(v_toApplicative_141_, 4);
v_isSharedCheck_211_ = !lean_is_exclusive(v_toApplicative_141_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_toApplicative_141_, 1);
lean_dec(v_unused_212_);
v___x_150_ = v_toApplicative_141_;
v_isShared_151_ = v_isSharedCheck_211_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_toSeqRight_148_);
lean_inc(v_toSeqLeft_147_);
lean_inc(v_toSeq_146_);
lean_inc(v_toFunctor_145_);
lean_dec(v_toApplicative_141_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_211_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___x_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_161_; 
v___f_152_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
v___f_153_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_145_);
v___f_154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_154_, 0, v_toFunctor_145_);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_155_, 0, v_toFunctor_145_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___f_154_);
lean_ctor_set(v___x_156_, 1, v___f_155_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeqRight_148_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_158_, 0, v_toSeqLeft_147_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_159_, 0, v_toSeq_146_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v___f_157_);
lean_ctor_set(v___x_150_, 3, v___f_158_);
lean_ctor_set(v___x_150_, 2, v___f_159_);
lean_ctor_set(v___x_150_, 1, v___f_152_);
lean_ctor_set(v___x_150_, 0, v___x_156_);
v___x_161_ = v___x_150_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___f_152_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___f_159_);
lean_ctor_set(v_reuseFailAlloc_210_, 3, v___f_158_);
lean_ctor_set(v_reuseFailAlloc_210_, 4, v___f_157_);
v___x_161_ = v_reuseFailAlloc_210_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___f_153_);
lean_ctor_set(v___x_143_, 0, v___x_161_);
v___x_163_ = v___x_143_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___f_153_);
v___x_163_ = v_reuseFailAlloc_209_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_getMCtx_175_; lean_object* v_modifyMCtx_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_490__overap_182_; lean_object* v___x_183_; 
lean_inc_ref_n(v___x_163_, 7);
v___f_164_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_164_, 0, v___x_163_);
v___f_165_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_165_, 0, v___x_163_);
v___f_166_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_166_, 0, v___x_163_);
v___f_167_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_167_, 0, v___x_163_);
v___f_168_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_168_, 0, v___x_163_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___f_164_);
lean_ctor_set(v___x_169_, 1, v___f_165_);
v___x_170_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, v___x_163_);
v___x_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
lean_ctor_set(v___x_171_, 2, v___f_166_);
lean_ctor_set(v___x_171_, 3, v___f_167_);
lean_ctor_set(v___x_171_, 4, v___f_168_);
v___x_172_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_172_, 0, lean_box(0));
lean_closure_set(v___x_172_, 1, v___x_163_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_175_ = lean_ctor_get(v___x_174_, 0);
v_modifyMCtx_176_ = lean_ctor_get(v___x_174_, 1);
v___x_177_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_177_, 0, lean_box(0));
lean_closure_set(v___x_177_, 1, v___x_163_);
lean_inc(v_modifyMCtx_176_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_178_, 0, v_modifyMCtx_176_);
lean_closure_set(v___f_178_, 1, v___x_177_);
v___f_179_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
lean_inc(v_getMCtx_175_);
v___x_180_ = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(v___x_180_, 0, lean_box(0));
lean_closure_set(v___x_180_, 1, lean_box(0));
lean_closure_set(v___x_180_, 2, v_getMCtx_175_);
lean_closure_set(v___x_180_, 3, v___f_179_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___f_178_);
v___x_490__overap_182_ = l_Lean_instantiateMVars___redArg(v___x_173_, v___x_181_, v_e_117_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_183_ = lean_apply_5(v___x_490__overap_182_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_200_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_200_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_200_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_200_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
if (lean_obj_tag(v_a_184_) == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec_ref(v_k_118_);
v___x_188_ = lean_box(0);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v_val_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_val_192_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_val_192_);
lean_dec_ref(v_a_184_);
v___x_193_ = l_Lean_Expr_getAppFn(v_val_192_);
v___x_194_ = l_Lean_Expr_isMVar(v___x_193_);
lean_dec_ref(v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_del_object(v___x_186_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_195_ = lean_apply_6(v_k_118_, v_val_192_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_198_; 
lean_dec(v_val_192_);
lean_dec_ref(v_k_118_);
v___x_196_ = lean_box(0);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_196_);
v___x_198_ = v___x_186_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_k_118_);
v_a_201_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_183_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_183_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___boxed(lean_object* v_00_u03b1_215_, lean_object* v_e_216_, lean_object* v_k_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(v_00_u03b1_215_, v_e_216_, v_k_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(lean_object* v_e_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_319_, v_a_321_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_1014_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_1014_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_1014_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_Expr_cleanupAnnotations(v_a_326_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_335_);
goto v___jp_330_;
}
else
{
lean_object* v_arg_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_arg_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc_ref(v_arg_337_);
v___x_338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
v___x_340_ = l_Lean_Expr_isConstOf(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_Expr_isApp(v___x_338_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_338_);
lean_dec_ref(v_arg_337_);
goto v___jp_330_;
}
else
{
lean_object* v_arg_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_arg_342_ = lean_ctor_get(v___x_338_, 1);
lean_inc_ref(v_arg_342_);
v___x_343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_338_);
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3));
v___x_345_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5));
v___x_347_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11));
v___x_353_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
v___x_355_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
v___x_356_ = l_Lean_Expr_isApp(v___x_343_);
if (v___x_356_ == 0)
{
lean_dec_ref(v___x_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
goto v___jp_330_;
}
else
{
lean_object* v_arg_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_arg_357_ = lean_ctor_get(v___x_343_, 1);
lean_inc_ref(v_arg_357_);
v___x_358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_343_);
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16));
v___x_360_ = l_Lean_Expr_isConstOf(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
v___x_361_ = l_Lean_Expr_isApp(v___x_358_);
if (v___x_361_ == 0)
{
lean_dec_ref(v___x_358_);
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
goto v___jp_330_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_358_);
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18));
v___x_364_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20));
v___x_366_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22));
v___x_368_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26));
v___x_372_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
v___x_374_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_373_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_Expr_isApp(v___x_362_);
if (v___x_375_ == 0)
{
lean_dec_ref(v___x_362_);
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
goto v___jp_330_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_362_);
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30));
v___x_378_ = l_Lean_Expr_isConstOf(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; 
v___x_379_ = l_Lean_Expr_isApp(v___x_376_);
if (v___x_379_ == 0)
{
lean_dec_ref(v___x_376_);
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
goto v___jp_330_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_376_);
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33));
v___x_382_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36));
v___x_384_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39));
v___x_386_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42));
v___x_388_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45));
v___x_390_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
v___x_392_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_391_);
lean_dec_ref(v___x_380_);
if (v___x_392_ == 0)
{
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
goto v___jp_330_;
}
else
{
lean_object* v___x_393_; 
lean_del_object(v___x_328_);
v___x_393_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_425_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_425_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_425_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_425_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; 
v___x_398_ = lean_unbox(v_a_394_);
lean_dec(v_a_394_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_399_ = lean_box(0);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
lean_object* v___x_403_; 
lean_del_object(v___x_396_);
v___x_403_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
if (lean_obj_tag(v_a_404_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_403_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_406_; 
lean_dec_ref(v___x_403_);
v_val_405_ = lean_ctor_get(v_a_404_, 0);
lean_inc(v_val_405_);
lean_dec_ref(v_a_404_);
v___x_406_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
if (lean_obj_tag(v_a_407_) == 0)
{
lean_dec(v_val_405_);
return v___x_406_;
}
else
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_406_, 0);
lean_dec(v_unused_424_);
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
else
{
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_422_; 
v_val_411_ = lean_ctor_get(v_a_407_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_422_ == 0)
{
v___x_413_ = v_a_407_;
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v_a_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_nat_add(v_val_405_, v_val_411_);
lean_dec(v_val_411_);
lean_dec(v_val_405_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_417_);
v___x_419_ = v___x_409_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
else
{
lean_dec(v_val_405_);
return v___x_406_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_426_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_393_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_393_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v___x_434_; 
lean_dec_ref(v___x_380_);
lean_del_object(v___x_328_);
v___x_434_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_466_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_466_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_466_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_466_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_440_ = lean_box(0);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_440_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_444_; 
lean_del_object(v___x_437_);
v___x_444_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
if (lean_obj_tag(v_a_445_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_444_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_447_; 
lean_dec_ref(v___x_444_);
v_val_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v_a_445_);
v___x_447_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
if (lean_obj_tag(v_a_448_) == 0)
{
lean_dec(v_val_446_);
return v___x_447_;
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_447_, 0);
lean_dec(v_unused_465_);
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
else
{
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_463_; 
v_val_452_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_463_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_nat_sub(v_val_446_, v_val_452_);
lean_dec(v_val_452_);
lean_dec(v_val_446_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_458_);
v___x_460_ = v___x_450_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
else
{
lean_dec(v_val_446_);
return v___x_447_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_444_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_467_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_434_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_434_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_object* v___x_475_; 
lean_dec_ref(v___x_380_);
lean_del_object(v___x_328_);
v___x_475_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_507_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_507_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_507_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_507_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint8_t v___x_480_; 
v___x_480_ = lean_unbox(v_a_476_);
lean_dec(v_a_476_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_481_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_481_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v___x_485_; 
lean_del_object(v___x_478_);
v___x_485_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
if (lean_obj_tag(v_a_486_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_485_;
}
else
{
lean_object* v_val_487_; lean_object* v___x_488_; 
lean_dec_ref(v___x_485_);
v_val_487_ = lean_ctor_get(v_a_486_, 0);
lean_inc(v_val_487_);
lean_dec_ref(v_a_486_);
v___x_488_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
if (lean_obj_tag(v_a_489_) == 0)
{
lean_dec(v_val_487_);
return v___x_488_;
}
else
{
lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_488_, 0);
lean_dec(v_unused_506_);
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_505_;
goto v_resetjp_490_;
}
else
{
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_505_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_504_; 
v_val_493_ = lean_ctor_get(v_a_489_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_489_);
if (v_isSharedCheck_504_ == 0)
{
v___x_495_ = v_a_489_;
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v_a_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_nat_mul(v_val_487_, v_val_493_);
lean_dec(v_val_493_);
lean_dec(v_val_487_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_499_);
v___x_501_ = v___x_491_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
else
{
lean_dec(v_val_487_);
return v___x_488_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_508_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_475_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_475_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
else
{
lean_object* v___x_516_; 
lean_dec_ref(v___x_380_);
lean_del_object(v___x_328_);
v___x_516_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_548_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_548_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_548_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_548_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; 
v___x_521_ = lean_unbox(v_a_517_);
lean_dec(v_a_517_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_522_ = lean_box(0);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_522_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; 
lean_del_object(v___x_519_);
v___x_526_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
if (lean_obj_tag(v_a_527_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_526_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_529_; 
lean_dec_ref(v___x_526_);
v_val_528_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_val_528_);
lean_dec_ref(v_a_527_);
v___x_529_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
if (lean_obj_tag(v_a_530_) == 0)
{
lean_dec(v_val_528_);
return v___x_529_;
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_546_; 
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v___x_529_, 0);
lean_dec(v_unused_547_);
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_546_;
goto v_resetjp_531_;
}
else
{
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_546_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_val_534_ = lean_ctor_get(v_a_530_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_530_);
if (v_isSharedCheck_545_ == 0)
{
v___x_536_ = v_a_530_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v_a_530_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_nat_div(v_val_528_, v_val_534_);
lean_dec(v_val_534_);
lean_dec(v_val_528_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_540_);
v___x_542_ = v___x_532_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
else
{
lean_dec(v_val_528_);
return v___x_529_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_549_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_516_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_516_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
else
{
lean_object* v___x_557_; 
lean_dec_ref(v___x_380_);
lean_del_object(v___x_328_);
v___x_557_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_589_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_589_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_589_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_589_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint8_t v___x_562_; 
v___x_562_ = lean_unbox(v_a_558_);
lean_dec(v_a_558_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_563_ = lean_box(0);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_563_);
v___x_565_ = v___x_560_;
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
else
{
lean_object* v___x_567_; 
lean_del_object(v___x_560_);
v___x_567_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
if (lean_obj_tag(v_a_568_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_567_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_570_; 
lean_dec_ref(v___x_567_);
v_val_569_ = lean_ctor_get(v_a_568_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v_a_568_);
v___x_570_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
if (lean_obj_tag(v_a_571_) == 0)
{
lean_dec(v_val_569_);
return v___x_570_;
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_570_, 0);
lean_dec(v_unused_588_);
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_587_;
goto v_resetjp_572_;
}
else
{
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_587_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_586_; 
v_val_575_ = lean_ctor_get(v_a_571_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_571_);
if (v_isSharedCheck_586_ == 0)
{
v___x_577_ = v_a_571_;
v_isShared_578_ = v_isSharedCheck_586_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v_a_571_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_586_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_nat_mod(v_val_569_, v_val_575_);
lean_dec(v_val_575_);
lean_dec(v_val_569_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_581_);
v___x_583_ = v___x_573_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
else
{
lean_dec(v_val_569_);
return v___x_570_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_567_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_590_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_557_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_557_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec_ref(v___x_380_);
lean_del_object(v___x_328_);
v___x_598_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_609_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_609_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___x_603_; 
v___x_603_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_604_ = lean_box(0);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___x_608_; 
lean_del_object(v___x_601_);
v___x_608_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_342_, v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_608_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_610_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_598_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_598_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v___x_376_);
lean_del_object(v___x_328_);
v___x_618_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_629_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_629_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; 
v___x_623_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_624_ = lean_box(0);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v___x_628_; 
lean_del_object(v___x_621_);
v___x_628_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_342_, v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_628_;
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_630_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_618_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_618_);
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
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_362_);
lean_del_object(v___x_328_);
v___x_638_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_670_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_670_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_670_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_670_;
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
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
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
v___x_648_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
if (lean_obj_tag(v_a_649_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_648_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_651_; 
lean_dec_ref(v___x_648_);
v_val_650_ = lean_ctor_get(v_a_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref(v_a_649_);
v___x_651_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
if (lean_obj_tag(v_a_652_) == 0)
{
lean_dec(v_val_650_);
return v___x_651_;
}
else
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_668_; 
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_651_, 0);
lean_dec(v_unused_669_);
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_668_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_668_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_val_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_667_; 
v_val_656_ = lean_ctor_get(v_a_652_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_a_652_);
if (v_isSharedCheck_667_ == 0)
{
v___x_658_ = v_a_652_;
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_val_656_);
lean_dec(v_a_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_nat_add(v_val_650_, v_val_656_);
lean_dec(v_val_656_);
lean_dec(v_val_650_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_662_);
v___x_664_ = v___x_654_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
else
{
lean_dec(v_val_650_);
return v___x_651_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_671_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_638_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_638_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_object* v___x_679_; 
lean_dec_ref(v___x_362_);
lean_del_object(v___x_328_);
v___x_679_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_711_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_711_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_711_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_711_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_687_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_685_ = lean_box(0);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v___x_689_; 
lean_del_object(v___x_682_);
v___x_689_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
if (lean_obj_tag(v_a_690_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_689_;
}
else
{
lean_object* v_val_691_; lean_object* v___x_692_; 
lean_dec_ref(v___x_689_);
v_val_691_ = lean_ctor_get(v_a_690_, 0);
lean_inc(v_val_691_);
lean_dec_ref(v_a_690_);
v___x_692_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
if (lean_obj_tag(v_a_693_) == 0)
{
lean_dec(v_val_691_);
return v___x_692_;
}
else
{
lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_692_, 0);
lean_dec(v_unused_710_);
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
else
{
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_val_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_708_; 
v_val_697_ = lean_ctor_get(v_a_693_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_708_ == 0)
{
v___x_699_ = v_a_693_;
v_isShared_700_ = v_isSharedCheck_708_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_val_697_);
lean_dec(v_a_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_708_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_nat_sub(v_val_691_, v_val_697_);
lean_dec(v_val_697_);
lean_dec(v_val_691_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_703_);
v___x_705_ = v___x_695_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
else
{
lean_dec(v_val_691_);
return v___x_692_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_712_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_679_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_679_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v___x_720_; 
lean_dec_ref(v___x_362_);
lean_del_object(v___x_328_);
v___x_720_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_752_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_752_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_752_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_752_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
uint8_t v___x_725_; 
v___x_725_ = lean_unbox(v_a_721_);
lean_dec(v_a_721_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_726_ = lean_box(0);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_726_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v___x_730_; 
lean_del_object(v___x_723_);
v___x_730_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
if (lean_obj_tag(v_a_731_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_730_;
}
else
{
lean_object* v_val_732_; lean_object* v___x_733_; 
lean_dec_ref(v___x_730_);
v_val_732_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_val_732_);
lean_dec_ref(v_a_731_);
v___x_733_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
if (lean_obj_tag(v_a_734_) == 0)
{
lean_dec(v_val_732_);
return v___x_733_;
}
else
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_750_; 
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_733_, 0);
lean_dec(v_unused_751_);
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_750_;
goto v_resetjp_735_;
}
else
{
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_750_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_val_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_749_; 
v_val_738_ = lean_ctor_get(v_a_734_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_749_ == 0)
{
v___x_740_ = v_a_734_;
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_val_738_);
lean_dec(v_a_734_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_nat_mul(v_val_732_, v_val_738_);
lean_dec(v_val_738_);
lean_dec(v_val_732_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_744_);
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
else
{
lean_dec(v_val_732_);
return v___x_733_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_753_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_720_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_720_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v___x_362_);
lean_del_object(v___x_328_);
v___x_761_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_793_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_793_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_793_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_793_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
uint8_t v___x_766_; 
v___x_766_ = lean_unbox(v_a_762_);
lean_dec(v_a_762_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_767_ = lean_box(0);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
lean_object* v___x_771_; 
lean_del_object(v___x_764_);
v___x_771_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
if (lean_obj_tag(v_a_772_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_771_;
}
else
{
lean_object* v_val_773_; lean_object* v___x_774_; 
lean_dec_ref(v___x_771_);
v_val_773_ = lean_ctor_get(v_a_772_, 0);
lean_inc(v_val_773_);
lean_dec_ref(v_a_772_);
v___x_774_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
if (lean_obj_tag(v_a_775_) == 0)
{
lean_dec(v_val_773_);
return v___x_774_;
}
else
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_791_; 
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_792_);
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
else
{
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_val_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_790_; 
v_val_779_ = lean_ctor_get(v_a_775_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_775_);
if (v_isSharedCheck_790_ == 0)
{
v___x_781_ = v_a_775_;
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_val_779_);
lean_dec(v_a_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_nat_div(v_val_773_, v_val_779_);
lean_dec(v_val_779_);
lean_dec(v_val_773_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_785_);
v___x_787_ = v___x_777_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
else
{
lean_dec(v_val_773_);
return v___x_774_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_794_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_761_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_761_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v___x_802_; 
lean_dec_ref(v___x_362_);
lean_del_object(v___x_328_);
v___x_802_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_834_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_834_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_834_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_834_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_808_ = lean_box(0);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v___x_812_; 
lean_del_object(v___x_805_);
v___x_812_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
if (lean_obj_tag(v_a_813_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_812_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_815_; 
lean_dec_ref(v___x_812_);
v_val_814_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v_a_813_);
v___x_815_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
if (lean_obj_tag(v_a_816_) == 0)
{
lean_dec(v_val_814_);
return v___x_815_;
}
else
{
lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_832_; 
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_815_, 0);
lean_dec(v_unused_833_);
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_832_;
goto v_resetjp_817_;
}
else
{
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_832_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_831_; 
v_val_820_ = lean_ctor_get(v_a_816_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_831_ == 0)
{
v___x_822_ = v_a_816_;
v_isShared_823_ = v_isSharedCheck_831_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v_a_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_831_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_nat_mod(v_val_814_, v_val_820_);
lean_dec(v_val_820_);
lean_dec(v_val_814_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_830_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_826_);
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
else
{
lean_dec(v_val_814_);
return v___x_815_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_835_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_802_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_802_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
else
{
lean_object* v___x_843_; 
lean_dec_ref(v___x_362_);
lean_del_object(v___x_328_);
v___x_843_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_357_, v_a_321_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_854_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_854_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v___x_848_; 
v___x_848_ = lean_unbox(v_a_844_);
lean_dec(v_a_844_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v___x_849_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v___x_853_; 
lean_del_object(v___x_846_);
v___x_853_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_342_, v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_853_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_337_);
v_a_855_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_843_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_843_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
else
{
lean_object* v___x_863_; 
lean_dec_ref(v___x_358_);
lean_dec_ref(v_arg_357_);
lean_del_object(v___x_328_);
v___x_863_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_337_, v_a_321_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_874_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; 
v___x_868_ = lean_unbox(v_a_864_);
lean_dec(v_a_864_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec_ref(v_arg_342_);
v___x_869_ = lean_box(0);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_873_; 
lean_del_object(v___x_866_);
v___x_873_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_873_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_arg_342_);
v_a_875_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_863_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_863_);
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
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_328_);
v___x_883_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
if (lean_obj_tag(v_a_884_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_883_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_886_; 
lean_dec_ref(v___x_883_);
v_val_885_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref(v_a_884_);
v___x_886_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
if (lean_obj_tag(v_a_887_) == 0)
{
lean_dec(v_val_885_);
return v___x_886_;
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_903_; 
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v___x_886_, 0);
lean_dec(v_unused_904_);
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_903_;
goto v_resetjp_888_;
}
else
{
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_903_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_902_; 
v_val_891_ = lean_ctor_get(v_a_887_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_902_ == 0)
{
v___x_893_ = v_a_887_;
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v_a_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_nat_add(v_val_885_, v_val_891_);
lean_dec(v_val_891_);
lean_dec(v_val_885_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_897_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
else
{
lean_dec(v_val_885_);
return v___x_886_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_883_;
}
}
}
else
{
lean_object* v___x_905_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_328_);
v___x_905_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
if (lean_obj_tag(v_a_906_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_905_;
}
else
{
lean_object* v_val_907_; lean_object* v___x_908_; 
lean_dec_ref(v___x_905_);
v_val_907_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_val_907_);
lean_dec_ref(v_a_906_);
v___x_908_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
if (lean_obj_tag(v_a_909_) == 0)
{
lean_dec(v_val_907_);
return v___x_908_;
}
else
{
lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_925_; 
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_926_);
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_925_;
goto v_resetjp_910_;
}
else
{
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_925_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_924_; 
v_val_913_ = lean_ctor_get(v_a_909_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_a_909_);
if (v_isSharedCheck_924_ == 0)
{
v___x_915_ = v_a_909_;
v_isShared_916_ = v_isSharedCheck_924_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v_a_909_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_924_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_nat_sub(v_val_907_, v_val_913_);
lean_dec(v_val_913_);
lean_dec(v_val_907_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_919_);
v___x_921_ = v___x_911_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
lean_dec(v_val_907_);
return v___x_908_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_905_;
}
}
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_328_);
v___x_927_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
if (lean_obj_tag(v_a_928_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_927_;
}
else
{
lean_object* v_val_929_; lean_object* v___x_930_; 
lean_dec_ref(v___x_927_);
v_val_929_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_val_929_);
lean_dec_ref(v_a_928_);
v___x_930_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
if (lean_obj_tag(v_a_931_) == 0)
{
lean_dec(v_val_929_);
return v___x_930_;
}
else
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_947_; 
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_948_);
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
else
{
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_946_; 
v_val_935_ = lean_ctor_get(v_a_931_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_946_ == 0)
{
v___x_937_ = v_a_931_;
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v_a_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_nat_mul(v_val_929_, v_val_935_);
lean_dec(v_val_935_);
lean_dec(v_val_929_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_941_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
else
{
lean_dec(v_val_929_);
return v___x_930_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_927_;
}
}
}
else
{
lean_object* v___x_949_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_328_);
v___x_949_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
if (lean_obj_tag(v_a_950_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_949_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_952_; 
lean_dec_ref(v___x_949_);
v_val_951_ = lean_ctor_get(v_a_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref(v_a_950_);
v___x_952_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
if (lean_obj_tag(v_a_953_) == 0)
{
lean_dec(v_val_951_);
return v___x_952_;
}
else
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_969_; 
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_970_);
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
else
{
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
v_val_957_ = lean_ctor_get(v_a_953_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_968_ == 0)
{
v___x_959_ = v_a_953_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v_a_953_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_nat_div(v_val_951_, v_val_957_);
lean_dec(v_val_957_);
lean_dec(v_val_951_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_963_);
v___x_965_ = v___x_955_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
else
{
lean_dec(v_val_951_);
return v___x_952_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_949_;
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_328_);
v___x_971_ = l_Lean_Meta_evalNat(v_arg_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
if (lean_obj_tag(v_a_972_) == 0)
{
lean_dec_ref(v_arg_337_);
return v___x_971_;
}
else
{
lean_object* v_val_973_; lean_object* v___x_974_; 
lean_dec_ref(v___x_971_);
v_val_973_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_val_973_);
lean_dec_ref(v_a_972_);
v___x_974_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
if (lean_obj_tag(v_a_975_) == 0)
{
lean_dec(v_val_973_);
return v___x_974_;
}
else
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_991_; 
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_974_, 0);
lean_dec(v_unused_992_);
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v_val_979_ = lean_ctor_get(v_a_975_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_a_975_);
if (v_isSharedCheck_990_ == 0)
{
v___x_981_ = v_a_975_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v_a_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_nat_mod(v_val_973_, v_val_979_);
lean_dec(v_val_979_);
lean_dec(v_val_973_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
else
{
lean_dec(v_val_973_);
return v___x_974_;
}
}
}
else
{
lean_dec_ref(v_arg_337_);
return v___x_971_;
}
}
}
else
{
lean_object* v___x_993_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_328_);
v___x_993_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_arg_342_, v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_993_;
}
}
}
else
{
lean_object* v___x_994_; 
lean_dec_ref(v___x_338_);
lean_del_object(v___x_328_);
v___x_994_ = l_Lean_Meta_evalNat(v_arg_337_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
if (lean_obj_tag(v_a_995_) == 0)
{
return v___x_994_;
}
else
{
lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_994_, 0);
lean_dec(v_unused_1013_);
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1012_;
goto v_resetjp_996_;
}
else
{
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1012_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1011_; 
v_val_999_ = lean_ctor_get(v_a_995_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1001_ = v_a_995_;
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v_a_995_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_val_999_, v___x_1003_);
lean_dec(v_val_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1006_);
v___x_1008_ = v___x_997_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
else
{
return v___x_994_;
}
}
}
v___jp_330_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_box(0);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_325_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_325_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
switch(lean_obj_tag(v_e_1023_))
{
case 9:
{
lean_object* v_a_1032_; 
v_a_1032_ = lean_ctor_get(v_e_1023_, 0);
lean_inc_ref(v_a_1032_);
lean_dec_ref(v_e_1023_);
if (lean_obj_tag(v_a_1032_) == 0)
{
lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
v_val_1033_ = lean_ctor_get(v_a_1032_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_a_1032_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1035_ = v_a_1032_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v_a_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_val_1033_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
else
{
lean_dec_ref(v_a_1032_);
goto v___jp_1029_;
}
}
case 10:
{
lean_object* v_expr_1042_; 
v_expr_1042_ = lean_ctor_get(v_e_1023_, 1);
lean_inc_ref(v_expr_1042_);
lean_dec_ref(v_e_1023_);
v_e_1023_ = v_expr_1042_;
goto _start;
}
case 4:
{
lean_object* v_declName_1044_; 
v_declName_1044_ = lean_ctor_get(v_e_1023_, 0);
lean_inc(v_declName_1044_);
lean_dec_ref(v_e_1023_);
if (lean_obj_tag(v_declName_1044_) == 1)
{
lean_object* v_pre_1045_; 
v_pre_1045_ = lean_ctor_get(v_declName_1044_, 0);
lean_inc(v_pre_1045_);
if (lean_obj_tag(v_pre_1045_) == 1)
{
lean_object* v_pre_1046_; 
v_pre_1046_ = lean_ctor_get(v_pre_1045_, 0);
if (lean_obj_tag(v_pre_1046_) == 0)
{
lean_object* v_str_1047_; lean_object* v_str_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_str_1047_ = lean_ctor_get(v_declName_1044_, 1);
lean_inc_ref(v_str_1047_);
lean_dec_ref(v_declName_1044_);
v_str_1048_ = lean_ctor_get(v_pre_1045_, 1);
lean_inc_ref(v_str_1048_);
lean_dec_ref(v_pre_1045_);
v___x_1049_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__0));
v___x_1050_ = lean_string_dec_eq(v_str_1048_, v___x_1049_);
lean_dec_ref(v_str_1048_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v_str_1047_);
goto v___jp_1029_;
}
else
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__1));
v___x_1052_ = lean_string_dec_eq(v_str_1047_, v___x_1051_);
lean_dec_ref(v_str_1047_);
if (v___x_1052_ == 0)
{
goto v___jp_1029_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Meta_evalNat___closed__2));
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
else
{
lean_dec_ref(v_pre_1045_);
lean_dec_ref(v_declName_1044_);
goto v___jp_1029_;
}
}
else
{
lean_dec_ref(v_declName_1044_);
lean_dec(v_pre_1045_);
goto v___jp_1029_;
}
}
else
{
lean_dec(v_declName_1044_);
goto v___jp_1029_;
}
}
case 5:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1055_;
}
case 2:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1056_;
}
default: 
{
lean_dec_ref(v_e_1023_);
goto v___jp_1029_;
}
}
v___jp_1029_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(lean_object* v_b_1057_, lean_object* v_n_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_evalNat(v_n_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
if (lean_obj_tag(v_a_1065_) == 0)
{
lean_dec_ref(v_b_1057_);
return v___x_1064_;
}
else
{
lean_object* v_val_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v___x_1064_);
v_val_1066_ = lean_ctor_get(v_a_1065_, 0);
lean_inc_n(v_val_1066_, 2);
lean_dec_ref(v_a_1065_);
v___x_1067_ = 1;
v___x_1068_ = l_Lean_checkExponent(v_val_1066_, v___x_1067_, v_a_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1097_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1097_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1097_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_unbox(v_a_1069_);
lean_dec(v_a_1069_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_dec(v_val_1066_);
lean_dec_ref(v_b_1057_);
v___x_1074_ = lean_box(0);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1078_; 
lean_del_object(v___x_1071_);
v___x_1078_ = l_Lean_Meta_evalNat(v_b_1057_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
if (lean_obj_tag(v_a_1079_) == 0)
{
lean_dec(v_val_1066_);
return v___x_1078_;
}
else
{
lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1095_; 
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1078_, 0);
lean_dec(v_unused_1096_);
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1095_;
goto v_resetjp_1080_;
}
else
{
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1095_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1094_; 
v_val_1083_ = lean_ctor_get(v_a_1079_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_a_1079_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1085_ = v_a_1079_;
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v_a_1079_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_nat_pow(v_val_1083_, v_val_1066_);
lean_dec(v_val_1066_);
lean_dec(v_val_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1089_);
v___x_1091_ = v___x_1081_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1066_);
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_val_1066_);
lean_dec_ref(v_b_1057_);
v_a_1098_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1068_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1068_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_1057_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(lean_object* v_b_1106_, lean_object* v_n_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(v_b_1106_, v_n_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object* v_e_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_evalNat(v_e_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(lean_object* v_e_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(v_e_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(lean_object* v_k_1128_, uint8_t v_allowLevelAssignments_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1129_, v_k_1128_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v_a_1144_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1135_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1135_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_object* v_00_u03b1_1161_, lean_object* v_k_1162_, uint8_t v_allowLevelAssignments_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v_k_1162_, v_allowLevelAssignments_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(lean_object* v_00_u03b1_1170_, lean_object* v_k_1171_, lean_object* v_allowLevelAssignments_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1178_; lean_object* v_res_1179_; 
v_allowLevelAssignments_boxed_1178_ = lean_unbox(v_allowLevelAssignments_1172_);
v_res_1179_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(v_00_u03b1_1170_, v_k_1171_, v_allowLevelAssignments_boxed_1178_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t v___x_1180_, lean_object* v_e_1181_, lean_object* v_inst_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; uint8_t v_foApprox_1189_; uint8_t v_ctxApprox_1190_; uint8_t v_quasiPatternApprox_1191_; uint8_t v_constApprox_1192_; uint8_t v_isDefEqStuckEx_1193_; uint8_t v_unificationHints_1194_; uint8_t v_proofIrrelevance_1195_; uint8_t v_assignSyntheticOpaque_1196_; uint8_t v_offsetCnstrs_1197_; uint8_t v_etaStruct_1198_; uint8_t v_univApprox_1199_; uint8_t v_iota_1200_; uint8_t v_beta_1201_; uint8_t v_proj_1202_; uint8_t v_zeta_1203_; uint8_t v_zetaDelta_1204_; uint8_t v_zetaUnused_1205_; uint8_t v_zetaHave_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1245_; 
v___x_1188_ = l_Lean_Meta_Context_config(v___y_1183_);
v_foApprox_1189_ = lean_ctor_get_uint8(v___x_1188_, 0);
v_ctxApprox_1190_ = lean_ctor_get_uint8(v___x_1188_, 1);
v_quasiPatternApprox_1191_ = lean_ctor_get_uint8(v___x_1188_, 2);
v_constApprox_1192_ = lean_ctor_get_uint8(v___x_1188_, 3);
v_isDefEqStuckEx_1193_ = lean_ctor_get_uint8(v___x_1188_, 4);
v_unificationHints_1194_ = lean_ctor_get_uint8(v___x_1188_, 5);
v_proofIrrelevance_1195_ = lean_ctor_get_uint8(v___x_1188_, 6);
v_assignSyntheticOpaque_1196_ = lean_ctor_get_uint8(v___x_1188_, 7);
v_offsetCnstrs_1197_ = lean_ctor_get_uint8(v___x_1188_, 8);
v_etaStruct_1198_ = lean_ctor_get_uint8(v___x_1188_, 10);
v_univApprox_1199_ = lean_ctor_get_uint8(v___x_1188_, 11);
v_iota_1200_ = lean_ctor_get_uint8(v___x_1188_, 12);
v_beta_1201_ = lean_ctor_get_uint8(v___x_1188_, 13);
v_proj_1202_ = lean_ctor_get_uint8(v___x_1188_, 14);
v_zeta_1203_ = lean_ctor_get_uint8(v___x_1188_, 15);
v_zetaDelta_1204_ = lean_ctor_get_uint8(v___x_1188_, 16);
v_zetaUnused_1205_ = lean_ctor_get_uint8(v___x_1188_, 17);
v_zetaHave_1206_ = lean_ctor_get_uint8(v___x_1188_, 18);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1208_ = v___x_1188_;
v_isShared_1209_ = v_isSharedCheck_1245_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v___x_1188_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1245_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint8_t v_trackZetaDelta_1210_; lean_object* v_zetaDeltaSet_1211_; lean_object* v_lctx_1212_; lean_object* v_localInstances_1213_; lean_object* v_defEqCtx_x3f_1214_; lean_object* v_synthPendingDepth_1215_; lean_object* v_canUnfold_x3f_1216_; uint8_t v_univApprox_1217_; uint8_t v_inTypeClassResolution_1218_; uint8_t v_cacheInferType_1219_; lean_object* v_config_1221_; 
v_trackZetaDelta_1210_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*7);
v_zetaDeltaSet_1211_ = lean_ctor_get(v___y_1183_, 1);
lean_inc(v_zetaDeltaSet_1211_);
v_lctx_1212_ = lean_ctor_get(v___y_1183_, 2);
lean_inc_ref(v_lctx_1212_);
v_localInstances_1213_ = lean_ctor_get(v___y_1183_, 3);
lean_inc_ref(v_localInstances_1213_);
v_defEqCtx_x3f_1214_ = lean_ctor_get(v___y_1183_, 4);
lean_inc(v_defEqCtx_x3f_1214_);
v_synthPendingDepth_1215_ = lean_ctor_get(v___y_1183_, 5);
lean_inc(v_synthPendingDepth_1215_);
v_canUnfold_x3f_1216_ = lean_ctor_get(v___y_1183_, 6);
lean_inc(v_canUnfold_x3f_1216_);
v_univApprox_1217_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1218_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*7 + 2);
v_cacheInferType_1219_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*7 + 3);
if (v_isShared_1209_ == 0)
{
v_config_1221_ = v___x_1208_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 0, v_foApprox_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 1, v_ctxApprox_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 2, v_quasiPatternApprox_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 3, v_constApprox_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 4, v_isDefEqStuckEx_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 5, v_unificationHints_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 6, v_proofIrrelevance_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 7, v_assignSyntheticOpaque_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 8, v_offsetCnstrs_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 10, v_etaStruct_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 11, v_univApprox_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 12, v_iota_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 13, v_beta_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 14, v_proj_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 15, v_zeta_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 16, v_zetaDelta_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 17, v_zetaUnused_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, 18, v_zetaHave_1206_);
v_config_1221_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
uint64_t v___x_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1236_; 
lean_ctor_set_uint8(v_config_1221_, 9, v___x_1180_);
v___x_1222_ = l_Lean_Meta_Context_configKey(v___y_1183_);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___y_1183_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; lean_object* v_unused_1241_; lean_object* v_unused_1242_; lean_object* v_unused_1243_; 
v_unused_1237_ = lean_ctor_get(v___y_1183_, 6);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v___y_1183_, 5);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v___y_1183_, 4);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v___y_1183_, 3);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v___y_1183_, 2);
lean_dec(v_unused_1241_);
v_unused_1242_ = lean_ctor_get(v___y_1183_, 1);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v___y_1183_, 0);
lean_dec(v_unused_1243_);
v___x_1224_ = v___y_1183_;
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___y_1183_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v___x_1229_; uint64_t v_key_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1226_ = 2ULL;
v___x_1227_ = lean_uint64_shift_right(v___x_1222_, v___x_1226_);
v___x_1228_ = lean_uint64_shift_left(v___x_1227_, v___x_1226_);
v___x_1229_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1180_);
v_key_1230_ = lean_uint64_lor(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1231_, 0, v_config_1221_);
lean_ctor_set_uint64(v___x_1231_, sizeof(void*)*1, v_key_1230_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1231_);
v___x_1233_ = v___x_1224_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_zetaDeltaSet_1211_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_lctx_1212_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_localInstances_1213_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_defEqCtx_x3f_1214_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v_synthPendingDepth_1215_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_canUnfold_x3f_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*7, v_trackZetaDelta_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*7 + 1, v_univApprox_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*7 + 3, v_cacheInferType_1219_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_isExprDefEq(v_e_1181_, v_inst_1182_, v___x_1233_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec_ref(v___x_1233_);
return v___x_1234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object* v___x_1246_, lean_object* v_e_1247_, lean_object* v_inst_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
uint8_t v___x_680__boxed_1254_; lean_object* v_res_1255_; 
v___x_680__boxed_1254_ = lean_unbox(v___x_1246_);
v_res_1255_ = l_Lean_Meta_matchesInstance___lam__0(v___x_680__boxed_1254_, v_e_1247_, v_inst_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object* v_e_1256_, lean_object* v_inst_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1263_ = 3;
v___x_1264_ = lean_box(v___x_1263_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Meta_matchesInstance___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1265_, 0, v___x_1264_);
lean_closure_set(v___f_1265_, 1, v_e_1256_);
lean_closure_set(v___f_1265_, 2, v_inst_1257_);
v___x_1266_ = 0;
v___x_1267_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___f_1265_, v___x_1266_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___boxed(lean_object* v_e_1268_, lean_object* v_inst_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_matchesInstance(v_e_1268_, v_inst_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object* v_e_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1276_, v_a_1278_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1444_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1444_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1444_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = l_Lean_Expr_cleanupAnnotations(v_a_1283_);
v___x_1293_ = l_Lean_Expr_isApp(v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v___x_1292_);
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_arg_1294_ = lean_ctor_get(v___x_1292_, 1);
lean_inc_ref(v_arg_1294_);
v___x_1295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1292_);
v___x_1296_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
v___x_1297_ = l_Lean_Expr_isConstOf(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Lean_Expr_isApp(v___x_1295_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___x_1295_);
lean_dec_ref(v_arg_1294_);
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1299_; lean_object* v_b_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_arg_1299_ = lean_ctor_get(v___x_1295_, 1);
lean_inc_ref(v_arg_1299_);
v___x_1359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1295_);
v___x_1360_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
v___x_1361_ = l_Lean_Expr_isConstOf(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Lean_Expr_isApp(v___x_1359_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v___x_1359_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
goto v___jp_1287_;
}
else
{
lean_object* v_arg_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_arg_1363_ = lean_ctor_get(v___x_1359_, 1);
lean_inc_ref(v_arg_1363_);
v___x_1364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1359_);
v___x_1365_ = l_Lean_Expr_isApp(v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v_arg_1363_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
goto v___jp_1287_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1364_);
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
v___x_1368_ = l_Lean_Expr_isConstOf(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_Expr_isApp(v___x_1366_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_arg_1363_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
goto v___jp_1287_;
}
else
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1366_);
v___x_1371_ = l_Lean_Expr_isApp(v___x_1370_);
if (v___x_1371_ == 0)
{
lean_dec_ref(v___x_1370_);
lean_dec_ref(v_arg_1363_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
goto v___jp_1287_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1370_);
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
v___x_1374_ = l_Lean_Expr_isConstOf(v___x_1372_, v___x_1373_);
lean_dec_ref(v___x_1372_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v_arg_1363_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
goto v___jp_1287_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_del_object(v___x_1285_);
v___x_1375_ = l_Lean_Nat_mkInstHAdd;
v___x_1376_ = l_Lean_Meta_matchesInstance(v_arg_1363_, v___x_1375_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1386_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_unbox(v_a_1377_);
lean_dec(v_a_1377_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
v___x_1382_ = lean_box(0);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_del_object(v___x_1379_);
v_b_1301_ = v_arg_1294_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
goto v___jp_1300_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
v_a_1387_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1376_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1376_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1366_);
lean_del_object(v___x_1285_);
v___x_1395_ = l_Lean_Nat_mkInstAdd;
v___x_1396_ = l_Lean_Meta_matchesInstance(v_arg_1363_, v___x_1395_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1406_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_unbox(v_a_1397_);
lean_dec(v_a_1397_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
v___x_1402_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_del_object(v___x_1399_);
v_b_1301_ = v_arg_1294_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
goto v___jp_1300_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1294_);
v_a_1407_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1396_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1396_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1359_);
lean_del_object(v___x_1285_);
v_b_1301_ = v_arg_1294_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
goto v___jp_1300_;
}
v___jp_1300_:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Meta_evalNat(v_b_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1350_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1350_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1350_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
if (lean_obj_tag(v_a_1307_) == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec_ref(v_arg_1299_);
v___x_1311_ = lean_box(0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
else
{
lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1309_);
v_val_1315_ = lean_ctor_get(v_a_1307_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_a_1307_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1317_ = v_a_1307_;
v_isShared_1318_ = v_isSharedCheck_1349_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_dec(v_a_1307_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1349_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_arg_1299_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1340_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1340_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1340_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_fst_1324_; lean_object* v_snd_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1339_; 
v_fst_1324_ = lean_ctor_get(v_a_1320_, 0);
v_snd_1325_ = lean_ctor_get(v_a_1320_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1327_ = v_a_1320_;
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_snd_1325_);
lean_inc(v_fst_1324_);
lean_dec(v_a_1320_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_nat_add(v_snd_1325_, v_val_1315_);
lean_dec(v_val_1315_);
lean_dec(v_snd_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_fst_1324_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1331_);
v___x_1333_ = v___x_1317_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1333_);
v___x_1335_ = v___x_1322_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_del_object(v___x_1317_);
lean_dec(v_val_1315_);
v_a_1341_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1319_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1319_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_arg_1299_);
v_a_1351_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1306_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1306_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
else
{
lean_object* v___x_1415_; 
lean_dec_ref(v___x_1295_);
lean_del_object(v___x_1285_);
v___x_1415_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_arg_1294_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1435_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1435_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1435_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1434_; 
v_fst_1420_ = lean_ctor_get(v_a_1416_, 0);
v_snd_1421_ = lean_ctor_get(v_a_1416_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1423_ = v_a_1416_;
v_isShared_1424_ = v_isSharedCheck_1434_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_inc(v_fst_1420_);
lean_dec(v_a_1416_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1434_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_add(v_snd_1421_, v___x_1425_);
lean_dec(v_snd_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1426_);
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_fst_1420_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1429_);
v___x_1431_ = v___x_1418_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1415_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1415_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
v___jp_1287_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v_a_1445_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1282_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1282_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* v_e_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1459_; 
lean_inc_ref(v_e_1453_);
v___x_1459_ = l_Lean_Meta_isOffset_x3f(v_e_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1473_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1473_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1473_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_e_1453_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1465_);
v___x_1467_ = v___x_1462_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_object* v_val_1469_; lean_object* v___x_1471_; 
lean_dec_ref(v_e_1453_);
v_val_1469_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_val_1469_);
lean_dec_ref(v_a_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v_val_1469_);
v___x_1471_ = v___x_1462_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_val_1469_);
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
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_e_1453_);
v_a_1474_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1459_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1459_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object* v_e_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(v_e_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f___boxed(lean_object* v_e_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Meta_isOffset_x3f(v_e_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Meta_evalNat(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1519_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1519_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1519_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
if (lean_obj_tag(v_a_1503_) == 1)
{
lean_object* v_val_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_val_1507_ = lean_ctor_get(v_a_1503_, 0);
lean_inc(v_val_1507_);
lean_dec_ref(v_a_1503_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_nat_dec_eq(v_val_1507_, v___x_1508_);
lean_dec(v_val_1507_);
v___x_1510_ = lean_box(v___x_1509_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1510_);
v___x_1512_ = v___x_1505_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
else
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
lean_dec(v_a_1503_);
v___x_1514_ = 0;
v___x_1515_ = lean_box(v___x_1514_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1515_);
v___x_1517_ = v___x_1505_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1502_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1502_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object* v_e_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOffset(lean_object* v_e_1535_, lean_object* v_offset_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_nat_dec_eq(v_offset_1536_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_inc_ref(v_e_1535_);
v___x_1544_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(v_e_1535_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1559_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1559_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1559_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1550_ = l_Lean_mkNatLit(v_offset_1536_);
v___x_1551_ = l_Lean_mkNatAdd(v_e_1535_, v___x_1550_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1551_);
v___x_1553_ = v___x_1547_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_dec_ref(v_e_1535_);
v___x_1555_ = l_Lean_mkNatLit(v_offset_1536_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1555_);
v___x_1557_ = v___x_1547_;
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
lean_dec(v_offset_1536_);
lean_dec_ref(v_e_1535_);
v_a_1560_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1544_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1544_);
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
else
{
lean_object* v___x_1568_; 
lean_dec(v_offset_1536_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_e_1535_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOffset___boxed(lean_object* v_e_1569_, lean_object* v_offset_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_Meta_mkOffset(v_e_1569_, v_offset_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object* v_s_1577_, lean_object* v_t_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_is_expr_def_eq(v_s_1577_, v_t_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1595_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1595_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1595_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
uint8_t v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1589_ = lean_unbox(v_a_1585_);
lean_dec(v_a_1585_);
v___x_1590_ = l_Bool_toLBool(v___x_1589_);
v___x_1591_ = lean_box(v___x_1590_);
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
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_a_1596_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1584_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1584_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0___boxed(lean_object* v_s_1604_, lean_object* v_t_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Meta_isDefEqOffset___lam__0(v_s_1604_, v_t_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(uint8_t v___x_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_box(v___x_1612_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1___boxed(lean_object* v___x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v___x_3572__boxed_1626_; lean_object* v_res_1627_; 
v___x_3572__boxed_1626_ = lean_unbox(v___x_1620_);
v_res_1627_ = l_Lean_Meta_isDefEqOffset___lam__1(v___x_3572__boxed_1626_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1627_;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___closed__1(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__0));
v___x_1632_ = l_Lean_mkConst(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object* v_s_1636_, lean_object* v_t_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_x_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v_s_1684_; lean_object* v_t_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___x_1691_; uint8_t v_offsetCnstrs_1692_; 
v___x_1691_ = l_Lean_Meta_Context_config(v_a_1638_);
v_offsetCnstrs_1692_ = lean_ctor_get_uint8(v___x_1691_, 8);
lean_dec_ref(v___x_1691_);
if (v_offsetCnstrs_1692_ == 0)
{
uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec_ref(v_t_1637_);
lean_dec_ref(v_s_1636_);
v___x_1693_ = 2;
v___x_1694_ = lean_box(v___x_1693_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; 
lean_inc_ref(v_s_1636_);
v___x_1696_ = l_Lean_Meta_isOffset_x3f(v_s_1636_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
if (lean_obj_tag(v_a_1697_) == 0)
{
lean_object* v___x_1698_; 
lean_inc_ref(v_s_1636_);
v___x_1698_ = l_Lean_Meta_evalNat(v_s_1636_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1750_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1750_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1750_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
if (lean_obj_tag(v_a_1699_) == 0)
{
uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_dec_ref(v_t_1637_);
lean_dec_ref(v_s_1636_);
v___x_1703_ = 2;
v___x_1704_ = lean_box(v___x_1703_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_object* v_val_1708_; lean_object* v___x_1709_; 
lean_del_object(v___x_1701_);
v_val_1708_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_val_1708_);
lean_dec_ref(v_a_1699_);
lean_inc_ref(v_t_1637_);
v___x_1709_ = l_Lean_Meta_isOffset_x3f(v_t_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref(v___x_1709_);
if (lean_obj_tag(v_a_1710_) == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_evalNat(v_t_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1726_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
if (lean_obj_tag(v_a_1712_) == 0)
{
uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_dec(v_val_1708_);
lean_dec_ref(v_s_1636_);
v___x_1716_ = 2;
v___x_1717_ = lean_box(v___x_1716_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v_val_1721_; uint8_t v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; 
lean_del_object(v___x_1714_);
v_val_1721_ = lean_ctor_get(v_a_1712_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v_a_1712_);
v___x_1722_ = lean_nat_dec_eq(v_val_1708_, v_val_1721_);
lean_dec(v_val_1721_);
lean_dec(v_val_1708_);
v___x_1723_ = l_Bool_toLBool(v___x_1722_);
v___x_1724_ = lean_box(v___x_1723_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1725_, 0, v___x_1724_);
v_x_1644_ = v___f_1725_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
goto v___jp_1643_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_val_1708_);
lean_dec_ref(v_s_1636_);
v_a_1727_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1711_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1711_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_val_1735_; lean_object* v_fst_1736_; lean_object* v_snd_1737_; uint8_t v___x_1738_; 
lean_dec_ref(v_t_1637_);
v_val_1735_ = lean_ctor_get(v_a_1710_, 0);
lean_inc(v_val_1735_);
lean_dec_ref(v_a_1710_);
v_fst_1736_ = lean_ctor_get(v_val_1735_, 0);
lean_inc(v_fst_1736_);
v_snd_1737_ = lean_ctor_get(v_val_1735_, 1);
lean_inc(v_snd_1737_);
lean_dec(v_val_1735_);
v___x_1738_ = lean_nat_dec_le(v_snd_1737_, v_val_1708_);
if (v___x_1738_ == 0)
{
lean_object* v___f_1739_; 
lean_dec(v_snd_1737_);
lean_dec(v_fst_1736_);
lean_dec(v_val_1708_);
v___f_1739_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
v_x_1644_ = v___f_1739_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_nat_sub(v_val_1708_, v_snd_1737_);
lean_dec(v_snd_1737_);
lean_dec(v_val_1708_);
v___x_1741_ = l_Lean_mkNatLit(v___x_1740_);
v_s_1684_ = v___x_1741_;
v_t_1685_ = v_fst_1736_;
v___y_1686_ = v_a_1638_;
v___y_1687_ = v_a_1639_;
v___y_1688_ = v_a_1640_;
v___y_1689_ = v_a_1641_;
goto v___jp_1683_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_val_1708_);
lean_dec_ref(v_t_1637_);
lean_dec_ref(v_s_1636_);
v_a_1742_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1709_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1709_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v_t_1637_);
lean_dec_ref(v_s_1636_);
v_a_1751_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1698_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1698_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_val_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; 
v_val_1759_ = lean_ctor_get(v_a_1697_, 0);
lean_inc(v_val_1759_);
lean_dec_ref(v_a_1697_);
v_fst_1760_ = lean_ctor_get(v_val_1759_, 0);
lean_inc(v_fst_1760_);
v_snd_1761_ = lean_ctor_get(v_val_1759_, 1);
lean_inc(v_snd_1761_);
lean_dec(v_val_1759_);
lean_inc_ref(v_t_1637_);
v___x_1762_ = l_Lean_Meta_isOffset_x3f(v_t_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
if (lean_obj_tag(v_a_1763_) == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_evalNat(v_t_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1779_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1779_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1779_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
if (lean_obj_tag(v_a_1765_) == 0)
{
uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v_snd_1761_);
lean_dec(v_fst_1760_);
lean_dec_ref(v_s_1636_);
v___x_1769_ = 2;
v___x_1770_ = lean_box(v___x_1769_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
else
{
lean_object* v_val_1774_; uint8_t v___x_1775_; 
lean_del_object(v___x_1767_);
v_val_1774_ = lean_ctor_get(v_a_1765_, 0);
lean_inc(v_val_1774_);
lean_dec_ref(v_a_1765_);
v___x_1775_ = lean_nat_dec_le(v_snd_1761_, v_val_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___f_1776_; 
lean_dec(v_val_1774_);
lean_dec(v_snd_1761_);
lean_dec(v_fst_1760_);
v___f_1776_ = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
v_x_1644_ = v___f_1776_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_nat_sub(v_val_1774_, v_snd_1761_);
lean_dec(v_snd_1761_);
lean_dec(v_val_1774_);
v___x_1778_ = l_Lean_mkNatLit(v___x_1777_);
v_s_1684_ = v_fst_1760_;
v_t_1685_ = v___x_1778_;
v___y_1686_ = v_a_1638_;
v___y_1687_ = v_a_1639_;
v___y_1688_ = v_a_1640_;
v___y_1689_ = v_a_1641_;
goto v___jp_1683_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_snd_1761_);
lean_dec(v_fst_1760_);
lean_dec_ref(v_s_1636_);
v_a_1780_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1764_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1764_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_val_1788_; lean_object* v_fst_1789_; lean_object* v_snd_1790_; uint8_t v___x_1791_; 
lean_dec_ref(v_t_1637_);
v_val_1788_ = lean_ctor_get(v_a_1763_, 0);
lean_inc(v_val_1788_);
lean_dec_ref(v_a_1763_);
v_fst_1789_ = lean_ctor_get(v_val_1788_, 0);
lean_inc(v_fst_1789_);
v_snd_1790_ = lean_ctor_get(v_val_1788_, 1);
lean_inc(v_snd_1790_);
lean_dec(v_val_1788_);
v___x_1791_ = lean_nat_dec_eq(v_snd_1761_, v_snd_1790_);
if (v___x_1791_ == 0)
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_nat_dec_lt(v_snd_1761_, v_snd_1790_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_nat_sub(v_snd_1761_, v_snd_1790_);
lean_dec(v_snd_1790_);
lean_dec(v_snd_1761_);
v___x_1794_ = l_Lean_Meta_mkOffset(v_fst_1760_, v___x_1793_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v___x_1794_);
v_s_1684_ = v_a_1795_;
v_t_1685_ = v_fst_1789_;
v___y_1686_ = v_a_1638_;
v___y_1687_ = v_a_1639_;
v___y_1688_ = v_a_1640_;
v___y_1689_ = v_a_1641_;
goto v___jp_1683_;
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_fst_1789_);
lean_dec_ref(v_s_1636_);
v_a_1796_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1794_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_nat_sub(v_snd_1790_, v_snd_1761_);
lean_dec(v_snd_1761_);
lean_dec(v_snd_1790_);
v___x_1805_ = l_Lean_Meta_mkOffset(v_fst_1789_, v___x_1804_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
v_s_1684_ = v_fst_1760_;
v_t_1685_ = v_a_1806_;
v___y_1686_ = v_a_1638_;
v___y_1687_ = v_a_1639_;
v___y_1688_ = v_a_1640_;
v___y_1689_ = v_a_1641_;
goto v___jp_1683_;
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_fst_1760_);
lean_dec_ref(v_s_1636_);
v_a_1807_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1805_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1805_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
else
{
lean_dec(v_snd_1790_);
lean_dec(v_snd_1761_);
v_s_1684_ = v_fst_1760_;
v_t_1685_ = v_fst_1789_;
v___y_1686_ = v_a_1638_;
v___y_1687_ = v_a_1639_;
v___y_1688_ = v_a_1640_;
v___y_1689_ = v_a_1641_;
goto v___jp_1683_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_snd_1761_);
lean_dec(v_fst_1760_);
lean_dec_ref(v_t_1637_);
lean_dec_ref(v_s_1636_);
v_a_1815_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1762_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1762_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_t_1637_);
lean_dec_ref(v_s_1636_);
v_a_1823_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1696_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1696_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
v___jp_1643_:
{
lean_object* v___x_1649_; 
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
v___x_1649_ = lean_infer_type(v_s_1636_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = lean_obj_once(&l_Lean_Meta_isDefEqOffset___closed__1, &l_Lean_Meta_isDefEqOffset___closed__1_once, _init_l_Lean_Meta_isDefEqOffset___closed__1);
v___x_1652_ = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(v___x_1652_, 0, v_a_1650_);
lean_closure_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = 0;
v___x_1654_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___x_1652_, v___x_1653_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1666_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1666_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1666_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_unbox(v_a_1655_);
lean_dec(v_a_1655_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec_ref(v_x_1644_);
v___x_1660_ = 2;
v___x_1661_ = lean_box(v___x_1660_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1661_);
v___x_1663_ = v___x_1657_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
else
{
lean_object* v___x_1665_; 
lean_del_object(v___x_1657_);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
v___x_1665_ = lean_apply_5(v_x_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, lean_box(0));
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_x_1644_);
v_a_1667_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1654_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1654_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v_x_1644_);
v_a_1675_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1649_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1649_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
v___jp_1683_:
{
lean_object* v___f_1690_; 
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1690_, 0, v_s_1684_);
lean_closure_set(v___f_1690_, 1, v_t_1685_);
v_x_1644_ = v___f_1690_;
v___y_1645_ = v___y_1686_;
v___y_1646_ = v___y_1687_;
v___y_1647_ = v___y_1688_;
v___y_1648_ = v___y_1689_;
goto v___jp_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object* v_s_1831_, lean_object* v_t_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Meta_isDefEqOffset(v_s_1831_, v_t_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1838_;
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
