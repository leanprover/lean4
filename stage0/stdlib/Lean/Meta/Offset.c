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
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5_value;
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_OptionT_lift___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value)} };
static const lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstModNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstAdd;
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_isDefEqOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_isDefEqOffset___closed__0 = (const lean_object*)&l_Lean_Meta_isDefEqOffset___closed__0_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_isDefEqOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isDefEqOffset___closed__1;
static const lean_closure_object l_Lean_Meta_isDefEqOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_isDefEqOffset___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_isDefEqOffset___closed__2 = (const lean_object*)&l_Lean_Meta_isDefEqOffset___closed__2_value;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_117; 
x_8 = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
x_9 = lean_ctor_get(x_8, 0);
x_117 = !lean_is_exclusive(x_8);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_8, 1);
lean_dec(x_118);
x_10 = x_8;
x_11 = x_117;
goto block_116;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_114; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_114 = !lean_is_exclusive(x_9);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_9, 1);
lean_dec(x_115);
x_16 = x_9;
x_17 = x_114;
goto block_113;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
x_19 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_22);
lean_ctor_set(x_112, 1, x_18);
lean_ctor_set(x_112, 2, x_25);
lean_ctor_set(x_112, 3, x_24);
lean_ctor_set(x_112, 4, x_23);
x_26 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_26);
lean_ctor_set(x_110, 1, x_19);
x_27 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_107; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = lean_ctor_get(x_28, 0);
x_107 = !lean_is_exclusive(x_28);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_28, 1);
lean_dec(x_108);
x_30 = x_28;
x_31 = x_107;
goto block_106;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_104; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_104 = !lean_is_exclusive(x_29);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_29, 1);
lean_dec(x_105);
x_36 = x_29;
x_37 = x_104;
goto block_103;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
x_39 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_34);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_33);
if (x_37 == 0)
{
lean_ctor_set(x_36, 4, x_43);
lean_ctor_set(x_36, 3, x_44);
lean_ctor_set(x_36, 2, x_45);
lean_ctor_set(x_36, 1, x_38);
lean_ctor_set(x_36, 0, x_42);
x_46 = x_36;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_42);
lean_ctor_set(x_102, 1, x_38);
lean_ctor_set(x_102, 2, x_45);
lean_ctor_set(x_102, 3, x_44);
lean_ctor_set(x_102, 4, x_43);
x_46 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_47; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_39);
lean_ctor_set(x_30, 0, x_46);
x_47 = x_30;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_46);
lean_ctor_set(x_100, 1, x_39);
x_47 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_98; 
lean_inc_ref(x_47);
x_48 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_48, 0, x_47);
lean_inc_ref(x_47);
x_49 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_49, 0, x_47);
lean_inc_ref(x_47);
x_50 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_50, 0, x_47);
lean_inc_ref(x_47);
x_51 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_51, 0, x_47);
lean_inc_ref(x_47);
x_52 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_52, 0, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_inc_ref(x_47);
x_54 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_54, 0, lean_box(0));
lean_closure_set(x_54, 1, x_47);
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_50);
lean_ctor_set(x_55, 3, x_51);
lean_ctor_set(x_55, 4, x_52);
lean_inc_ref(x_47);
x_56 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, x_47);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_instMonadMCtxMetaM;
x_59 = lean_ctor_get(x_58, 0);
x_60 = lean_ctor_get(x_58, 1);
x_98 = !lean_is_exclusive(x_58);
if (x_98 == 0)
{
x_61 = x_58;
x_62 = x_98;
goto block_97;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_58);
x_61 = lean_box(0);
x_62 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_63, 0, lean_box(0));
lean_closure_set(x_63, 1, x_47);
x_64 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_64, 0, x_60);
lean_closure_set(x_64, 1, x_63);
x_65 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(x_66, 0, lean_box(0));
lean_closure_set(x_66, 1, lean_box(0));
lean_closure_set(x_66, 2, x_59);
lean_closure_set(x_66, 3, x_65);
if (x_62 == 0)
{
lean_ctor_set(x_61, 1, x_64);
lean_ctor_set(x_61, 0, x_66);
x_67 = x_61;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_66);
lean_ctor_set(x_96, 1, x_64);
x_67 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_instantiateMVars___redArg(x_57, x_67, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_69 = lean_apply_5(x_68, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_86; 
x_70 = lean_ctor_get(x_69, 0);
x_86 = !lean_is_exclusive(x_69);
if (x_86 == 0)
{
x_71 = x_69;
x_72 = x_86;
goto block_85;
}
else
{
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_86;
goto block_85;
}
block_85:
{
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_73 = lean_box(0);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_73);
x_74 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
lean_dec_ref(x_70);
x_78 = l_Lean_Expr_getAppFn(x_77);
x_79 = l_Lean_Expr_isMVar(x_78);
lean_dec_ref(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_del_object(x_71);
x_80 = lean_apply_6(x_2, x_77, x_3, x_4, x_5, x_6, lean_box(0));
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_81 = lean_box(0);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_81);
x_82 = x_71;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_69, 0);
x_94 = !lean_is_exclusive(x_69);
if (x_94 == 0)
{
x_88 = x_69;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_69);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_118; 
x_9 = lean_obj_once(&l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1, &l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once, _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
x_10 = lean_ctor_get(x_9, 0);
x_118 = !lean_is_exclusive(x_9);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_9, 1);
lean_dec(x_119);
x_11 = x_9;
x_12 = x_118;
goto block_117;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_115; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_115 = !lean_is_exclusive(x_10);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_10, 1);
lean_dec(x_116);
x_17 = x_10;
x_18 = x_115;
goto block_114;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2));
x_20 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3));
lean_inc_ref(x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_15);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_14);
if (x_18 == 0)
{
lean_ctor_set(x_17, 4, x_24);
lean_ctor_set(x_17, 3, x_25);
lean_ctor_set(x_17, 2, x_26);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_23);
x_27 = x_17;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_23);
lean_ctor_set(x_113, 1, x_19);
lean_ctor_set(x_113, 2, x_26);
lean_ctor_set(x_113, 3, x_25);
lean_ctor_set(x_113, 4, x_24);
x_27 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_28; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_27);
x_28 = x_11;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_27);
lean_ctor_set(x_111, 1, x_20);
x_28 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_108; 
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = lean_ctor_get(x_29, 0);
x_108 = !lean_is_exclusive(x_29);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_29, 1);
lean_dec(x_109);
x_31 = x_29;
x_32 = x_108;
goto block_107;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_105; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_105 = !lean_is_exclusive(x_30);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_30, 1);
lean_dec(x_106);
x_37 = x_30;
x_38 = x_105;
goto block_104;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4));
x_40 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5));
lean_inc_ref(x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_35);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_34);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_44);
lean_ctor_set(x_37, 3, x_45);
lean_ctor_set(x_37, 2, x_46);
lean_ctor_set(x_37, 1, x_39);
lean_ctor_set(x_37, 0, x_43);
x_47 = x_37;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_43);
lean_ctor_set(x_103, 1, x_39);
lean_ctor_set(x_103, 2, x_46);
lean_ctor_set(x_103, 3, x_45);
lean_ctor_set(x_103, 4, x_44);
x_47 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_48; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_40);
lean_ctor_set(x_31, 0, x_47);
x_48 = x_31;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_47);
lean_ctor_set(x_101, 1, x_40);
x_48 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_99; 
lean_inc_ref(x_48);
x_49 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_49, 0, x_48);
lean_inc_ref(x_48);
x_50 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_50, 0, x_48);
lean_inc_ref(x_48);
x_51 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_51, 0, x_48);
lean_inc_ref(x_48);
x_52 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_52, 0, x_48);
lean_inc_ref(x_48);
x_53 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_53, 0, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_inc_ref(x_48);
x_55 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_48);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_53);
lean_inc_ref(x_48);
x_57 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_57, 0, lean_box(0));
lean_closure_set(x_57, 1, x_48);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_instMonadMCtxMetaM;
x_60 = lean_ctor_get(x_59, 0);
x_61 = lean_ctor_get(x_59, 1);
x_99 = !lean_is_exclusive(x_59);
if (x_99 == 0)
{
x_62 = x_59;
x_63 = x_99;
goto block_98;
}
else
{
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_59);
x_62 = lean_box(0);
x_63 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_64, 0, lean_box(0));
lean_closure_set(x_64, 1, x_48);
x_65 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_65, 0, x_61);
lean_closure_set(x_65, 1, x_64);
x_66 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6));
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 4);
lean_closure_set(x_67, 0, lean_box(0));
lean_closure_set(x_67, 1, lean_box(0));
lean_closure_set(x_67, 2, x_60);
lean_closure_set(x_67, 3, x_66);
if (x_63 == 0)
{
lean_ctor_set(x_62, 1, x_65);
lean_ctor_set(x_62, 0, x_67);
x_68 = x_62;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_67);
lean_ctor_set(x_97, 1, x_65);
x_68 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_instantiateMVars___redArg(x_58, x_68, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_70 = lean_apply_5(x_69, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_87; 
x_71 = lean_ctor_get(x_70, 0);
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
x_72 = x_70;
x_73 = x_87;
goto block_86;
}
else
{
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = x_87;
goto block_86;
}
block_86:
{
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_74 = lean_box(0);
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_74);
x_75 = x_72;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_74);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec_ref(x_71);
x_79 = l_Lean_Expr_getAppFn(x_78);
x_80 = l_Lean_Expr_isMVar(x_79);
lean_dec_ref(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_del_object(x_72);
x_81 = lean_apply_6(x_3, x_78, x_4, x_5, x_6, x_7, lean_box(0));
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_78);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_82 = lean_box(0);
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_82);
x_83 = x_72;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_88 = lean_ctor_get(x_70, 0);
x_95 = !lean_is_exclusive(x_70);
if (x_95 == 0)
{
x_89 = x_70;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_70);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_696; 
x_8 = lean_ctor_get(x_7, 0);
x_696 = !lean_is_exclusive(x_7);
if (x_696 == 0)
{
x_9 = x_7;
x_10 = x_696;
goto block_695;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_696;
goto block_695;
}
block_695:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_8);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isApp(x_19);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_25 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3));
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5));
x_28 = l_Lean_Expr_isConstOf(x_24, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7));
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9));
x_32 = l_Lean_Expr_isConstOf(x_24, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11));
x_34 = l_Lean_Expr_isConstOf(x_24, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
x_36 = l_Lean_Expr_isConstOf(x_24, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_isApp(x_24);
if (x_37 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_38);
x_39 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_40 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16));
x_41 = l_Lean_Expr_isConstOf(x_39, x_40);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_isApp(x_39);
if (x_42 == 0)
{
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_39);
x_44 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18));
x_45 = l_Lean_Expr_isConstOf(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20));
x_47 = l_Lean_Expr_isConstOf(x_43, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22));
x_49 = l_Lean_Expr_isConstOf(x_43, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24));
x_51 = l_Lean_Expr_isConstOf(x_43, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26));
x_53 = l_Lean_Expr_isConstOf(x_43, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
x_55 = l_Lean_Expr_isConstOf(x_43, x_54);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_isApp(x_43);
if (x_56 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_38);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_58 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30));
x_59 = l_Lean_Expr_isConstOf(x_57, x_58);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_isApp(x_57);
if (x_60 == 0)
{
lean_dec_ref(x_57);
lean_dec_ref(x_38);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_62 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33));
x_63 = l_Lean_Expr_isConstOf(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36));
x_65 = l_Lean_Expr_isConstOf(x_61, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39));
x_67 = l_Lean_Expr_isConstOf(x_61, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42));
x_69 = l_Lean_Expr_isConstOf(x_61, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45));
x_71 = l_Lean_Expr_isConstOf(x_61, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
x_73 = l_Lean_Expr_isConstOf(x_61, x_72);
lean_dec_ref(x_61);
if (x_73 == 0)
{
lean_dec_ref(x_38);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
goto block_15;
}
else
{
lean_object* x_74; 
lean_del_object(x_9);
x_74 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_38, x_3);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_106; 
x_75 = lean_ctor_get(x_74, 0);
x_106 = !lean_is_exclusive(x_74);
if (x_106 == 0)
{
x_76 = x_74;
x_77 = x_106;
goto block_105;
}
else
{
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = x_106;
goto block_105;
}
block_105:
{
uint8_t x_78; 
x_78 = lean_unbox(x_75);
lean_dec(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_79 = lean_box(0);
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_79);
x_80 = x_76;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_79);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
else
{
lean_object* x_83; 
lean_del_object(x_76);
lean_inc_ref(x_4);
x_83 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_85);
return x_86;
}
else
{
lean_object* x_88; uint8_t x_89; uint8_t x_103; 
x_103 = !lean_is_exclusive(x_86);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_86, 0);
lean_dec(x_104);
x_88 = x_86;
x_89 = x_103;
goto block_102;
}
else
{
lean_dec(x_86);
x_88 = lean_box(0);
x_89 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_101; 
x_90 = lean_ctor_get(x_87, 0);
x_101 = !lean_is_exclusive(x_87);
if (x_101 == 0)
{
x_91 = x_87;
x_92 = x_101;
goto block_100;
}
else
{
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_box(0);
x_92 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_nat_add(x_85, x_90);
lean_dec(x_90);
lean_dec(x_85);
if (x_92 == 0)
{
lean_ctor_set(x_91, 0, x_93);
x_94 = x_91;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_93);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_89 == 0)
{
lean_ctor_set(x_88, 0, x_94);
x_95 = x_88;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_94);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
}
}
else
{
lean_dec(x_85);
return x_86;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_83;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_107 = lean_ctor_get(x_74, 0);
x_114 = !lean_is_exclusive(x_74);
if (x_114 == 0)
{
x_108 = x_74;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_74);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
}
else
{
lean_object* x_115; 
lean_dec_ref(x_61);
lean_del_object(x_9);
x_115 = l_Lean_Meta_Structural_isInstHSubNat___redArg(x_38, x_3);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_147; 
x_116 = lean_ctor_get(x_115, 0);
x_147 = !lean_is_exclusive(x_115);
if (x_147 == 0)
{
x_117 = x_115;
x_118 = x_147;
goto block_146;
}
else
{
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_box(0);
x_118 = x_147;
goto block_146;
}
block_146:
{
uint8_t x_119; 
x_119 = lean_unbox(x_116);
lean_dec(x_116);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_120 = lean_box(0);
if (x_118 == 0)
{
lean_ctor_set(x_117, 0, x_120);
x_121 = x_117;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
else
{
lean_object* x_124; 
lean_del_object(x_117);
lean_inc_ref(x_4);
x_124 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_126);
return x_127;
}
else
{
lean_object* x_129; uint8_t x_130; uint8_t x_144; 
x_144 = !lean_is_exclusive(x_127);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_127, 0);
lean_dec(x_145);
x_129 = x_127;
x_130 = x_144;
goto block_143;
}
else
{
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_142; 
x_131 = lean_ctor_get(x_128, 0);
x_142 = !lean_is_exclusive(x_128);
if (x_142 == 0)
{
x_132 = x_128;
x_133 = x_142;
goto block_141;
}
else
{
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_box(0);
x_133 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_nat_sub(x_126, x_131);
lean_dec(x_131);
lean_dec(x_126);
if (x_133 == 0)
{
lean_ctor_set(x_132, 0, x_134);
x_135 = x_132;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_134);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_130 == 0)
{
lean_ctor_set(x_129, 0, x_135);
x_136 = x_129;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_135);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
}
}
else
{
lean_dec(x_126);
return x_127;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_124;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_148 = lean_ctor_get(x_115, 0);
x_155 = !lean_is_exclusive(x_115);
if (x_155 == 0)
{
x_149 = x_115;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_115);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
else
{
lean_object* x_156; 
lean_dec_ref(x_61);
lean_del_object(x_9);
x_156 = l_Lean_Meta_Structural_isInstHMulNat___redArg(x_38, x_3);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_188; 
x_157 = lean_ctor_get(x_156, 0);
x_188 = !lean_is_exclusive(x_156);
if (x_188 == 0)
{
x_158 = x_156;
x_159 = x_188;
goto block_187;
}
else
{
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_box(0);
x_159 = x_188;
goto block_187;
}
block_187:
{
uint8_t x_160; 
x_160 = lean_unbox(x_157);
lean_dec(x_157);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_161 = lean_box(0);
if (x_159 == 0)
{
lean_ctor_set(x_158, 0, x_161);
x_162 = x_158;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_161);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
else
{
lean_object* x_165; 
lean_del_object(x_158);
lean_inc_ref(x_4);
x_165 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_dec(x_167);
return x_168;
}
else
{
lean_object* x_170; uint8_t x_171; uint8_t x_185; 
x_185 = !lean_is_exclusive(x_168);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_168, 0);
lean_dec(x_186);
x_170 = x_168;
x_171 = x_185;
goto block_184;
}
else
{
lean_dec(x_168);
x_170 = lean_box(0);
x_171 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_183; 
x_172 = lean_ctor_get(x_169, 0);
x_183 = !lean_is_exclusive(x_169);
if (x_183 == 0)
{
x_173 = x_169;
x_174 = x_183;
goto block_182;
}
else
{
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_box(0);
x_174 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_nat_mul(x_167, x_172);
lean_dec(x_172);
lean_dec(x_167);
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_175);
x_176 = x_173;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_175);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_171 == 0)
{
lean_ctor_set(x_170, 0, x_176);
x_177 = x_170;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_176);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
}
}
else
{
lean_dec(x_167);
return x_168;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_165;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_196; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_189 = lean_ctor_get(x_156, 0);
x_196 = !lean_is_exclusive(x_156);
if (x_196 == 0)
{
x_190 = x_156;
x_191 = x_196;
goto block_195;
}
else
{
lean_inc(x_189);
lean_dec(x_156);
x_190 = lean_box(0);
x_191 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_192; 
if (x_191 == 0)
{
x_192 = x_190;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_189);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
}
else
{
lean_object* x_197; 
lean_dec_ref(x_61);
lean_del_object(x_9);
x_197 = l_Lean_Meta_Structural_isInstHDivNat___redArg(x_38, x_3);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_229; 
x_198 = lean_ctor_get(x_197, 0);
x_229 = !lean_is_exclusive(x_197);
if (x_229 == 0)
{
x_199 = x_197;
x_200 = x_229;
goto block_228;
}
else
{
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_box(0);
x_200 = x_229;
goto block_228;
}
block_228:
{
uint8_t x_201; 
x_201 = lean_unbox(x_198);
lean_dec(x_198);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_202 = lean_box(0);
if (x_200 == 0)
{
lean_ctor_set(x_199, 0, x_202);
x_203 = x_199;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_202);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
else
{
lean_object* x_206; 
lean_del_object(x_199);
lean_inc_ref(x_4);
x_206 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_dec(x_208);
return x_209;
}
else
{
lean_object* x_211; uint8_t x_212; uint8_t x_226; 
x_226 = !lean_is_exclusive(x_209);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_209, 0);
lean_dec(x_227);
x_211 = x_209;
x_212 = x_226;
goto block_225;
}
else
{
lean_dec(x_209);
x_211 = lean_box(0);
x_212 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_224; 
x_213 = lean_ctor_get(x_210, 0);
x_224 = !lean_is_exclusive(x_210);
if (x_224 == 0)
{
x_214 = x_210;
x_215 = x_224;
goto block_223;
}
else
{
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_box(0);
x_215 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_nat_div(x_208, x_213);
lean_dec(x_213);
lean_dec(x_208);
if (x_215 == 0)
{
lean_ctor_set(x_214, 0, x_216);
x_217 = x_214;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_216);
x_217 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_218; 
if (x_212 == 0)
{
lean_ctor_set(x_211, 0, x_217);
x_218 = x_211;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_217);
x_218 = x_220;
goto block_219;
}
block_219:
{
return x_218;
}
}
}
}
}
}
else
{
lean_dec(x_208);
return x_209;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_206;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_237; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_230 = lean_ctor_get(x_197, 0);
x_237 = !lean_is_exclusive(x_197);
if (x_237 == 0)
{
x_231 = x_197;
x_232 = x_237;
goto block_236;
}
else
{
lean_inc(x_230);
lean_dec(x_197);
x_231 = lean_box(0);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_232 == 0)
{
x_233 = x_231;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_230);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
}
}
else
{
lean_object* x_238; 
lean_dec_ref(x_61);
lean_del_object(x_9);
x_238 = l_Lean_Meta_Structural_isInstHModNat___redArg(x_38, x_3);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_270; 
x_239 = lean_ctor_get(x_238, 0);
x_270 = !lean_is_exclusive(x_238);
if (x_270 == 0)
{
x_240 = x_238;
x_241 = x_270;
goto block_269;
}
else
{
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_box(0);
x_241 = x_270;
goto block_269;
}
block_269:
{
uint8_t x_242; 
x_242 = lean_unbox(x_239);
lean_dec(x_239);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_243 = lean_box(0);
if (x_241 == 0)
{
lean_ctor_set(x_240, 0, x_243);
x_244 = x_240;
goto block_245;
}
else
{
lean_object* x_246; 
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_243);
x_244 = x_246;
goto block_245;
}
block_245:
{
return x_244;
}
}
else
{
lean_object* x_247; 
lean_del_object(x_240);
lean_inc_ref(x_4);
x_247 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_247;
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_dec(x_249);
return x_250;
}
else
{
lean_object* x_252; uint8_t x_253; uint8_t x_267; 
x_267 = !lean_is_exclusive(x_250);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_250, 0);
lean_dec(x_268);
x_252 = x_250;
x_253 = x_267;
goto block_266;
}
else
{
lean_dec(x_250);
x_252 = lean_box(0);
x_253 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_265; 
x_254 = lean_ctor_get(x_251, 0);
x_265 = !lean_is_exclusive(x_251);
if (x_265 == 0)
{
x_255 = x_251;
x_256 = x_265;
goto block_264;
}
else
{
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_box(0);
x_256 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_nat_mod(x_249, x_254);
lean_dec(x_254);
lean_dec(x_249);
if (x_256 == 0)
{
lean_ctor_set(x_255, 0, x_257);
x_258 = x_255;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_257);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_253 == 0)
{
lean_ctor_set(x_252, 0, x_258);
x_259 = x_252;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_258);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
else
{
lean_dec(x_249);
return x_250;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_247;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_271 = lean_ctor_get(x_238, 0);
x_278 = !lean_is_exclusive(x_238);
if (x_278 == 0)
{
x_272 = x_238;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_238);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
}
else
{
lean_object* x_279; 
lean_dec_ref(x_61);
lean_del_object(x_9);
x_279 = l_Lean_Meta_Structural_isInstHPowNat___redArg(x_38, x_3);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_290; 
x_280 = lean_ctor_get(x_279, 0);
x_290 = !lean_is_exclusive(x_279);
if (x_290 == 0)
{
x_281 = x_279;
x_282 = x_290;
goto block_289;
}
else
{
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_box(0);
x_282 = x_290;
goto block_289;
}
block_289:
{
uint8_t x_283; 
x_283 = lean_unbox(x_280);
lean_dec(x_280);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_284 = lean_box(0);
if (x_282 == 0)
{
lean_ctor_set(x_281, 0, x_284);
x_285 = x_281;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_284);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
else
{
lean_object* x_288; 
lean_del_object(x_281);
x_288 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(x_23, x_18, x_2, x_3, x_4, x_5);
return x_288;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_298; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_291 = lean_ctor_get(x_279, 0);
x_298 = !lean_is_exclusive(x_279);
if (x_298 == 0)
{
x_292 = x_279;
x_293 = x_298;
goto block_297;
}
else
{
lean_inc(x_291);
lean_dec(x_279);
x_292 = lean_box(0);
x_293 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_294; 
if (x_293 == 0)
{
x_294 = x_292;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_291);
x_294 = x_296;
goto block_295;
}
block_295:
{
return x_294;
}
}
}
}
}
}
else
{
lean_object* x_299; 
lean_dec_ref(x_57);
lean_del_object(x_9);
x_299 = l_Lean_Meta_Structural_isInstPowNat___redArg(x_38, x_3);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_310; 
x_300 = lean_ctor_get(x_299, 0);
x_310 = !lean_is_exclusive(x_299);
if (x_310 == 0)
{
x_301 = x_299;
x_302 = x_310;
goto block_309;
}
else
{
lean_inc(x_300);
lean_dec(x_299);
x_301 = lean_box(0);
x_302 = x_310;
goto block_309;
}
block_309:
{
uint8_t x_303; 
x_303 = lean_unbox(x_300);
lean_dec(x_300);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_304 = lean_box(0);
if (x_302 == 0)
{
lean_ctor_set(x_301, 0, x_304);
x_305 = x_301;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_304);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
else
{
lean_object* x_308; 
lean_del_object(x_301);
x_308 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(x_23, x_18, x_2, x_3, x_4, x_5);
return x_308;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_318; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_311 = lean_ctor_get(x_299, 0);
x_318 = !lean_is_exclusive(x_299);
if (x_318 == 0)
{
x_312 = x_299;
x_313 = x_318;
goto block_317;
}
else
{
lean_inc(x_311);
lean_dec(x_299);
x_312 = lean_box(0);
x_313 = x_318;
goto block_317;
}
block_317:
{
lean_object* x_314; 
if (x_313 == 0)
{
x_314 = x_312;
goto block_315;
}
else
{
lean_object* x_316; 
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_311);
x_314 = x_316;
goto block_315;
}
block_315:
{
return x_314;
}
}
}
}
}
}
else
{
lean_object* x_319; 
lean_dec_ref(x_43);
lean_del_object(x_9);
x_319 = l_Lean_Meta_Structural_isInstAddNat___redArg(x_38, x_3);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_351; 
x_320 = lean_ctor_get(x_319, 0);
x_351 = !lean_is_exclusive(x_319);
if (x_351 == 0)
{
x_321 = x_319;
x_322 = x_351;
goto block_350;
}
else
{
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_box(0);
x_322 = x_351;
goto block_350;
}
block_350:
{
uint8_t x_323; 
x_323 = lean_unbox(x_320);
lean_dec(x_320);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_324 = lean_box(0);
if (x_322 == 0)
{
lean_ctor_set(x_321, 0, x_324);
x_325 = x_321;
goto block_326;
}
else
{
lean_object* x_327; 
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_324);
x_325 = x_327;
goto block_326;
}
block_326:
{
return x_325;
}
}
else
{
lean_object* x_328; 
lean_del_object(x_321);
lean_inc_ref(x_4);
x_328 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_obj_tag(x_329) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_328;
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec_ref(x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec_ref(x_329);
x_331 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
if (lean_obj_tag(x_332) == 0)
{
lean_dec(x_330);
return x_331;
}
else
{
lean_object* x_333; uint8_t x_334; uint8_t x_348; 
x_348 = !lean_is_exclusive(x_331);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_331, 0);
lean_dec(x_349);
x_333 = x_331;
x_334 = x_348;
goto block_347;
}
else
{
lean_dec(x_331);
x_333 = lean_box(0);
x_334 = x_348;
goto block_347;
}
block_347:
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; uint8_t x_346; 
x_335 = lean_ctor_get(x_332, 0);
x_346 = !lean_is_exclusive(x_332);
if (x_346 == 0)
{
x_336 = x_332;
x_337 = x_346;
goto block_345;
}
else
{
lean_inc(x_335);
lean_dec(x_332);
x_336 = lean_box(0);
x_337 = x_346;
goto block_345;
}
block_345:
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_nat_add(x_330, x_335);
lean_dec(x_335);
lean_dec(x_330);
if (x_337 == 0)
{
lean_ctor_set(x_336, 0, x_338);
x_339 = x_336;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_338);
x_339 = x_344;
goto block_343;
}
block_343:
{
lean_object* x_340; 
if (x_334 == 0)
{
lean_ctor_set(x_333, 0, x_339);
x_340 = x_333;
goto block_341;
}
else
{
lean_object* x_342; 
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_339);
x_340 = x_342;
goto block_341;
}
block_341:
{
return x_340;
}
}
}
}
}
}
else
{
lean_dec(x_330);
return x_331;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_328;
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; uint8_t x_359; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_352 = lean_ctor_get(x_319, 0);
x_359 = !lean_is_exclusive(x_319);
if (x_359 == 0)
{
x_353 = x_319;
x_354 = x_359;
goto block_358;
}
else
{
lean_inc(x_352);
lean_dec(x_319);
x_353 = lean_box(0);
x_354 = x_359;
goto block_358;
}
block_358:
{
lean_object* x_355; 
if (x_354 == 0)
{
x_355 = x_353;
goto block_356;
}
else
{
lean_object* x_357; 
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_352);
x_355 = x_357;
goto block_356;
}
block_356:
{
return x_355;
}
}
}
}
}
else
{
lean_object* x_360; 
lean_dec_ref(x_43);
lean_del_object(x_9);
x_360 = l_Lean_Meta_Structural_isInstSubNat___redArg(x_38, x_3);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_392; 
x_361 = lean_ctor_get(x_360, 0);
x_392 = !lean_is_exclusive(x_360);
if (x_392 == 0)
{
x_362 = x_360;
x_363 = x_392;
goto block_391;
}
else
{
lean_inc(x_361);
lean_dec(x_360);
x_362 = lean_box(0);
x_363 = x_392;
goto block_391;
}
block_391:
{
uint8_t x_364; 
x_364 = lean_unbox(x_361);
lean_dec(x_361);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_365 = lean_box(0);
if (x_363 == 0)
{
lean_ctor_set(x_362, 0, x_365);
x_366 = x_362;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_365);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
else
{
lean_object* x_369; 
lean_del_object(x_362);
lean_inc_ref(x_4);
x_369 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_369;
}
else
{
lean_object* x_371; lean_object* x_372; 
lean_dec_ref(x_369);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
lean_dec_ref(x_370);
x_372 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_dec(x_371);
return x_372;
}
else
{
lean_object* x_374; uint8_t x_375; uint8_t x_389; 
x_389 = !lean_is_exclusive(x_372);
if (x_389 == 0)
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_372, 0);
lean_dec(x_390);
x_374 = x_372;
x_375 = x_389;
goto block_388;
}
else
{
lean_dec(x_372);
x_374 = lean_box(0);
x_375 = x_389;
goto block_388;
}
block_388:
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_387; 
x_376 = lean_ctor_get(x_373, 0);
x_387 = !lean_is_exclusive(x_373);
if (x_387 == 0)
{
x_377 = x_373;
x_378 = x_387;
goto block_386;
}
else
{
lean_inc(x_376);
lean_dec(x_373);
x_377 = lean_box(0);
x_378 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_nat_sub(x_371, x_376);
lean_dec(x_376);
lean_dec(x_371);
if (x_378 == 0)
{
lean_ctor_set(x_377, 0, x_379);
x_380 = x_377;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_379);
x_380 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_381; 
if (x_375 == 0)
{
lean_ctor_set(x_374, 0, x_380);
x_381 = x_374;
goto block_382;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_383, 0, x_380);
x_381 = x_383;
goto block_382;
}
block_382:
{
return x_381;
}
}
}
}
}
}
else
{
lean_dec(x_371);
return x_372;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_369;
}
}
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_400; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_393 = lean_ctor_get(x_360, 0);
x_400 = !lean_is_exclusive(x_360);
if (x_400 == 0)
{
x_394 = x_360;
x_395 = x_400;
goto block_399;
}
else
{
lean_inc(x_393);
lean_dec(x_360);
x_394 = lean_box(0);
x_395 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_396; 
if (x_395 == 0)
{
x_396 = x_394;
goto block_397;
}
else
{
lean_object* x_398; 
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_393);
x_396 = x_398;
goto block_397;
}
block_397:
{
return x_396;
}
}
}
}
}
else
{
lean_object* x_401; 
lean_dec_ref(x_43);
lean_del_object(x_9);
x_401 = l_Lean_Meta_Structural_isInstMulNat___redArg(x_38, x_3);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_433; 
x_402 = lean_ctor_get(x_401, 0);
x_433 = !lean_is_exclusive(x_401);
if (x_433 == 0)
{
x_403 = x_401;
x_404 = x_433;
goto block_432;
}
else
{
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_box(0);
x_404 = x_433;
goto block_432;
}
block_432:
{
uint8_t x_405; 
x_405 = lean_unbox(x_402);
lean_dec(x_402);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_406 = lean_box(0);
if (x_404 == 0)
{
lean_ctor_set(x_403, 0, x_406);
x_407 = x_403;
goto block_408;
}
else
{
lean_object* x_409; 
x_409 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_409, 0, x_406);
x_407 = x_409;
goto block_408;
}
block_408:
{
return x_407;
}
}
else
{
lean_object* x_410; 
lean_del_object(x_403);
lean_inc_ref(x_4);
x_410 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
if (lean_obj_tag(x_411) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_410;
}
else
{
lean_object* x_412; lean_object* x_413; 
lean_dec_ref(x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
x_413 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 0)
{
lean_dec(x_412);
return x_413;
}
else
{
lean_object* x_415; uint8_t x_416; uint8_t x_430; 
x_430 = !lean_is_exclusive(x_413);
if (x_430 == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_413, 0);
lean_dec(x_431);
x_415 = x_413;
x_416 = x_430;
goto block_429;
}
else
{
lean_dec(x_413);
x_415 = lean_box(0);
x_416 = x_430;
goto block_429;
}
block_429:
{
lean_object* x_417; lean_object* x_418; uint8_t x_419; uint8_t x_428; 
x_417 = lean_ctor_get(x_414, 0);
x_428 = !lean_is_exclusive(x_414);
if (x_428 == 0)
{
x_418 = x_414;
x_419 = x_428;
goto block_427;
}
else
{
lean_inc(x_417);
lean_dec(x_414);
x_418 = lean_box(0);
x_419 = x_428;
goto block_427;
}
block_427:
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_nat_mul(x_412, x_417);
lean_dec(x_417);
lean_dec(x_412);
if (x_419 == 0)
{
lean_ctor_set(x_418, 0, x_420);
x_421 = x_418;
goto block_425;
}
else
{
lean_object* x_426; 
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_420);
x_421 = x_426;
goto block_425;
}
block_425:
{
lean_object* x_422; 
if (x_416 == 0)
{
lean_ctor_set(x_415, 0, x_421);
x_422 = x_415;
goto block_423;
}
else
{
lean_object* x_424; 
x_424 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_424, 0, x_421);
x_422 = x_424;
goto block_423;
}
block_423:
{
return x_422;
}
}
}
}
}
}
else
{
lean_dec(x_412);
return x_413;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_410;
}
}
}
}
else
{
lean_object* x_434; lean_object* x_435; uint8_t x_436; uint8_t x_441; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_434 = lean_ctor_get(x_401, 0);
x_441 = !lean_is_exclusive(x_401);
if (x_441 == 0)
{
x_435 = x_401;
x_436 = x_441;
goto block_440;
}
else
{
lean_inc(x_434);
lean_dec(x_401);
x_435 = lean_box(0);
x_436 = x_441;
goto block_440;
}
block_440:
{
lean_object* x_437; 
if (x_436 == 0)
{
x_437 = x_435;
goto block_438;
}
else
{
lean_object* x_439; 
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_434);
x_437 = x_439;
goto block_438;
}
block_438:
{
return x_437;
}
}
}
}
}
else
{
lean_object* x_442; 
lean_dec_ref(x_43);
lean_del_object(x_9);
x_442 = l_Lean_Meta_Structural_isInstDivNat___redArg(x_38, x_3);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; uint8_t x_474; 
x_443 = lean_ctor_get(x_442, 0);
x_474 = !lean_is_exclusive(x_442);
if (x_474 == 0)
{
x_444 = x_442;
x_445 = x_474;
goto block_473;
}
else
{
lean_inc(x_443);
lean_dec(x_442);
x_444 = lean_box(0);
x_445 = x_474;
goto block_473;
}
block_473:
{
uint8_t x_446; 
x_446 = lean_unbox(x_443);
lean_dec(x_443);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_447 = lean_box(0);
if (x_445 == 0)
{
lean_ctor_set(x_444, 0, x_447);
x_448 = x_444;
goto block_449;
}
else
{
lean_object* x_450; 
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_447);
x_448 = x_450;
goto block_449;
}
block_449:
{
return x_448;
}
}
else
{
lean_object* x_451; 
lean_del_object(x_444);
lean_inc_ref(x_4);
x_451 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
if (lean_obj_tag(x_452) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_451;
}
else
{
lean_object* x_453; lean_object* x_454; 
lean_dec_ref(x_451);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
lean_dec_ref(x_452);
x_454 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
if (lean_obj_tag(x_455) == 0)
{
lean_dec(x_453);
return x_454;
}
else
{
lean_object* x_456; uint8_t x_457; uint8_t x_471; 
x_471 = !lean_is_exclusive(x_454);
if (x_471 == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_454, 0);
lean_dec(x_472);
x_456 = x_454;
x_457 = x_471;
goto block_470;
}
else
{
lean_dec(x_454);
x_456 = lean_box(0);
x_457 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; uint8_t x_469; 
x_458 = lean_ctor_get(x_455, 0);
x_469 = !lean_is_exclusive(x_455);
if (x_469 == 0)
{
x_459 = x_455;
x_460 = x_469;
goto block_468;
}
else
{
lean_inc(x_458);
lean_dec(x_455);
x_459 = lean_box(0);
x_460 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_nat_div(x_453, x_458);
lean_dec(x_458);
lean_dec(x_453);
if (x_460 == 0)
{
lean_ctor_set(x_459, 0, x_461);
x_462 = x_459;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_467, 0, x_461);
x_462 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_463; 
if (x_457 == 0)
{
lean_ctor_set(x_456, 0, x_462);
x_463 = x_456;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_465, 0, x_462);
x_463 = x_465;
goto block_464;
}
block_464:
{
return x_463;
}
}
}
}
}
}
else
{
lean_dec(x_453);
return x_454;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_451;
}
}
}
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; uint8_t x_482; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_475 = lean_ctor_get(x_442, 0);
x_482 = !lean_is_exclusive(x_442);
if (x_482 == 0)
{
x_476 = x_442;
x_477 = x_482;
goto block_481;
}
else
{
lean_inc(x_475);
lean_dec(x_442);
x_476 = lean_box(0);
x_477 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_478; 
if (x_477 == 0)
{
x_478 = x_476;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_475);
x_478 = x_480;
goto block_479;
}
block_479:
{
return x_478;
}
}
}
}
}
else
{
lean_object* x_483; 
lean_dec_ref(x_43);
lean_del_object(x_9);
x_483 = l_Lean_Meta_Structural_isInstModNat___redArg(x_38, x_3);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; uint8_t x_515; 
x_484 = lean_ctor_get(x_483, 0);
x_515 = !lean_is_exclusive(x_483);
if (x_515 == 0)
{
x_485 = x_483;
x_486 = x_515;
goto block_514;
}
else
{
lean_inc(x_484);
lean_dec(x_483);
x_485 = lean_box(0);
x_486 = x_515;
goto block_514;
}
block_514:
{
uint8_t x_487; 
x_487 = lean_unbox(x_484);
lean_dec(x_484);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_488 = lean_box(0);
if (x_486 == 0)
{
lean_ctor_set(x_485, 0, x_488);
x_489 = x_485;
goto block_490;
}
else
{
lean_object* x_491; 
x_491 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_491, 0, x_488);
x_489 = x_491;
goto block_490;
}
block_490:
{
return x_489;
}
}
else
{
lean_object* x_492; 
lean_del_object(x_485);
lean_inc_ref(x_4);
x_492 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
if (lean_obj_tag(x_493) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_492;
}
else
{
lean_object* x_494; lean_object* x_495; 
lean_dec_ref(x_492);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec_ref(x_493);
x_495 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_dec(x_494);
return x_495;
}
else
{
lean_object* x_497; uint8_t x_498; uint8_t x_512; 
x_512 = !lean_is_exclusive(x_495);
if (x_512 == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_495, 0);
lean_dec(x_513);
x_497 = x_495;
x_498 = x_512;
goto block_511;
}
else
{
lean_dec(x_495);
x_497 = lean_box(0);
x_498 = x_512;
goto block_511;
}
block_511:
{
lean_object* x_499; lean_object* x_500; uint8_t x_501; uint8_t x_510; 
x_499 = lean_ctor_get(x_496, 0);
x_510 = !lean_is_exclusive(x_496);
if (x_510 == 0)
{
x_500 = x_496;
x_501 = x_510;
goto block_509;
}
else
{
lean_inc(x_499);
lean_dec(x_496);
x_500 = lean_box(0);
x_501 = x_510;
goto block_509;
}
block_509:
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_nat_mod(x_494, x_499);
lean_dec(x_499);
lean_dec(x_494);
if (x_501 == 0)
{
lean_ctor_set(x_500, 0, x_502);
x_503 = x_500;
goto block_507;
}
else
{
lean_object* x_508; 
x_508 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_508, 0, x_502);
x_503 = x_508;
goto block_507;
}
block_507:
{
lean_object* x_504; 
if (x_498 == 0)
{
lean_ctor_set(x_497, 0, x_503);
x_504 = x_497;
goto block_505;
}
else
{
lean_object* x_506; 
x_506 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_506, 0, x_503);
x_504 = x_506;
goto block_505;
}
block_505:
{
return x_504;
}
}
}
}
}
}
else
{
lean_dec(x_494);
return x_495;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_492;
}
}
}
}
else
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; uint8_t x_523; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_516 = lean_ctor_get(x_483, 0);
x_523 = !lean_is_exclusive(x_483);
if (x_523 == 0)
{
x_517 = x_483;
x_518 = x_523;
goto block_522;
}
else
{
lean_inc(x_516);
lean_dec(x_483);
x_517 = lean_box(0);
x_518 = x_523;
goto block_522;
}
block_522:
{
lean_object* x_519; 
if (x_518 == 0)
{
x_519 = x_517;
goto block_520;
}
else
{
lean_object* x_521; 
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_516);
x_519 = x_521;
goto block_520;
}
block_520:
{
return x_519;
}
}
}
}
}
else
{
lean_object* x_524; 
lean_dec_ref(x_43);
lean_del_object(x_9);
x_524 = l_Lean_Meta_Structural_isInstNatPowNat___redArg(x_38, x_3);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; uint8_t x_527; uint8_t x_535; 
x_525 = lean_ctor_get(x_524, 0);
x_535 = !lean_is_exclusive(x_524);
if (x_535 == 0)
{
x_526 = x_524;
x_527 = x_535;
goto block_534;
}
else
{
lean_inc(x_525);
lean_dec(x_524);
x_526 = lean_box(0);
x_527 = x_535;
goto block_534;
}
block_534:
{
uint8_t x_528; 
x_528 = lean_unbox(x_525);
lean_dec(x_525);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_529 = lean_box(0);
if (x_527 == 0)
{
lean_ctor_set(x_526, 0, x_529);
x_530 = x_526;
goto block_531;
}
else
{
lean_object* x_532; 
x_532 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_532, 0, x_529);
x_530 = x_532;
goto block_531;
}
block_531:
{
return x_530;
}
}
else
{
lean_object* x_533; 
lean_del_object(x_526);
x_533 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(x_23, x_18, x_2, x_3, x_4, x_5);
return x_533;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; uint8_t x_543; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
x_536 = lean_ctor_get(x_524, 0);
x_543 = !lean_is_exclusive(x_524);
if (x_543 == 0)
{
x_537 = x_524;
x_538 = x_543;
goto block_542;
}
else
{
lean_inc(x_536);
lean_dec(x_524);
x_537 = lean_box(0);
x_538 = x_543;
goto block_542;
}
block_542:
{
lean_object* x_539; 
if (x_538 == 0)
{
x_539 = x_537;
goto block_540;
}
else
{
lean_object* x_541; 
x_541 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_541, 0, x_536);
x_539 = x_541;
goto block_540;
}
block_540:
{
return x_539;
}
}
}
}
}
}
else
{
lean_object* x_544; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_del_object(x_9);
x_544 = l_Lean_Meta_Structural_isInstOfNatNat___redArg(x_18, x_3);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; uint8_t x_547; uint8_t x_555; 
x_545 = lean_ctor_get(x_544, 0);
x_555 = !lean_is_exclusive(x_544);
if (x_555 == 0)
{
x_546 = x_544;
x_547 = x_555;
goto block_554;
}
else
{
lean_inc(x_545);
lean_dec(x_544);
x_546 = lean_box(0);
x_547 = x_555;
goto block_554;
}
block_554:
{
uint8_t x_548; 
x_548 = lean_unbox(x_545);
lean_dec(x_545);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
lean_dec_ref(x_23);
lean_dec_ref(x_4);
x_549 = lean_box(0);
if (x_547 == 0)
{
lean_ctor_set(x_546, 0, x_549);
x_550 = x_546;
goto block_551;
}
else
{
lean_object* x_552; 
x_552 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_552, 0, x_549);
x_550 = x_552;
goto block_551;
}
block_551:
{
return x_550;
}
}
else
{
lean_object* x_553; 
lean_del_object(x_546);
x_553 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
return x_553;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; uint8_t x_558; uint8_t x_563; 
lean_dec_ref(x_23);
lean_dec_ref(x_4);
x_556 = lean_ctor_get(x_544, 0);
x_563 = !lean_is_exclusive(x_544);
if (x_563 == 0)
{
x_557 = x_544;
x_558 = x_563;
goto block_562;
}
else
{
lean_inc(x_556);
lean_dec(x_544);
x_557 = lean_box(0);
x_558 = x_563;
goto block_562;
}
block_562:
{
lean_object* x_559; 
if (x_558 == 0)
{
x_559 = x_557;
goto block_560;
}
else
{
lean_object* x_561; 
x_561 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_561, 0, x_556);
x_559 = x_561;
goto block_560;
}
block_560:
{
return x_559;
}
}
}
}
}
}
else
{
lean_object* x_564; 
lean_dec_ref(x_24);
lean_del_object(x_9);
lean_inc_ref(x_4);
x_564 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
if (lean_obj_tag(x_565) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_564;
}
else
{
lean_object* x_566; lean_object* x_567; 
lean_dec_ref(x_564);
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
lean_dec_ref(x_565);
x_567 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
if (lean_obj_tag(x_568) == 0)
{
lean_dec(x_566);
return x_567;
}
else
{
lean_object* x_569; uint8_t x_570; uint8_t x_584; 
x_584 = !lean_is_exclusive(x_567);
if (x_584 == 0)
{
lean_object* x_585; 
x_585 = lean_ctor_get(x_567, 0);
lean_dec(x_585);
x_569 = x_567;
x_570 = x_584;
goto block_583;
}
else
{
lean_dec(x_567);
x_569 = lean_box(0);
x_570 = x_584;
goto block_583;
}
block_583:
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_582; 
x_571 = lean_ctor_get(x_568, 0);
x_582 = !lean_is_exclusive(x_568);
if (x_582 == 0)
{
x_572 = x_568;
x_573 = x_582;
goto block_581;
}
else
{
lean_inc(x_571);
lean_dec(x_568);
x_572 = lean_box(0);
x_573 = x_582;
goto block_581;
}
block_581:
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_nat_add(x_566, x_571);
lean_dec(x_571);
lean_dec(x_566);
if (x_573 == 0)
{
lean_ctor_set(x_572, 0, x_574);
x_575 = x_572;
goto block_579;
}
else
{
lean_object* x_580; 
x_580 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_580, 0, x_574);
x_575 = x_580;
goto block_579;
}
block_579:
{
lean_object* x_576; 
if (x_570 == 0)
{
lean_ctor_set(x_569, 0, x_575);
x_576 = x_569;
goto block_577;
}
else
{
lean_object* x_578; 
x_578 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_578, 0, x_575);
x_576 = x_578;
goto block_577;
}
block_577:
{
return x_576;
}
}
}
}
}
}
else
{
lean_dec(x_566);
return x_567;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_564;
}
}
}
else
{
lean_object* x_586; 
lean_dec_ref(x_24);
lean_del_object(x_9);
lean_inc_ref(x_4);
x_586 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
if (lean_obj_tag(x_587) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_586;
}
else
{
lean_object* x_588; lean_object* x_589; 
lean_dec_ref(x_586);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
lean_dec_ref(x_587);
x_589 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
if (lean_obj_tag(x_590) == 0)
{
lean_dec(x_588);
return x_589;
}
else
{
lean_object* x_591; uint8_t x_592; uint8_t x_606; 
x_606 = !lean_is_exclusive(x_589);
if (x_606 == 0)
{
lean_object* x_607; 
x_607 = lean_ctor_get(x_589, 0);
lean_dec(x_607);
x_591 = x_589;
x_592 = x_606;
goto block_605;
}
else
{
lean_dec(x_589);
x_591 = lean_box(0);
x_592 = x_606;
goto block_605;
}
block_605:
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_604; 
x_593 = lean_ctor_get(x_590, 0);
x_604 = !lean_is_exclusive(x_590);
if (x_604 == 0)
{
x_594 = x_590;
x_595 = x_604;
goto block_603;
}
else
{
lean_inc(x_593);
lean_dec(x_590);
x_594 = lean_box(0);
x_595 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_596; lean_object* x_597; 
x_596 = lean_nat_sub(x_588, x_593);
lean_dec(x_593);
lean_dec(x_588);
if (x_595 == 0)
{
lean_ctor_set(x_594, 0, x_596);
x_597 = x_594;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_602, 0, x_596);
x_597 = x_602;
goto block_601;
}
block_601:
{
lean_object* x_598; 
if (x_592 == 0)
{
lean_ctor_set(x_591, 0, x_597);
x_598 = x_591;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_600, 0, x_597);
x_598 = x_600;
goto block_599;
}
block_599:
{
return x_598;
}
}
}
}
}
}
else
{
lean_dec(x_588);
return x_589;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_586;
}
}
}
else
{
lean_object* x_608; 
lean_dec_ref(x_24);
lean_del_object(x_9);
lean_inc_ref(x_4);
x_608 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
if (lean_obj_tag(x_609) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_608;
}
else
{
lean_object* x_610; lean_object* x_611; 
lean_dec_ref(x_608);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
lean_dec_ref(x_609);
x_611 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
if (lean_obj_tag(x_612) == 0)
{
lean_dec(x_610);
return x_611;
}
else
{
lean_object* x_613; uint8_t x_614; uint8_t x_628; 
x_628 = !lean_is_exclusive(x_611);
if (x_628 == 0)
{
lean_object* x_629; 
x_629 = lean_ctor_get(x_611, 0);
lean_dec(x_629);
x_613 = x_611;
x_614 = x_628;
goto block_627;
}
else
{
lean_dec(x_611);
x_613 = lean_box(0);
x_614 = x_628;
goto block_627;
}
block_627:
{
lean_object* x_615; lean_object* x_616; uint8_t x_617; uint8_t x_626; 
x_615 = lean_ctor_get(x_612, 0);
x_626 = !lean_is_exclusive(x_612);
if (x_626 == 0)
{
x_616 = x_612;
x_617 = x_626;
goto block_625;
}
else
{
lean_inc(x_615);
lean_dec(x_612);
x_616 = lean_box(0);
x_617 = x_626;
goto block_625;
}
block_625:
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_nat_mul(x_610, x_615);
lean_dec(x_615);
lean_dec(x_610);
if (x_617 == 0)
{
lean_ctor_set(x_616, 0, x_618);
x_619 = x_616;
goto block_623;
}
else
{
lean_object* x_624; 
x_624 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_624, 0, x_618);
x_619 = x_624;
goto block_623;
}
block_623:
{
lean_object* x_620; 
if (x_614 == 0)
{
lean_ctor_set(x_613, 0, x_619);
x_620 = x_613;
goto block_621;
}
else
{
lean_object* x_622; 
x_622 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_622, 0, x_619);
x_620 = x_622;
goto block_621;
}
block_621:
{
return x_620;
}
}
}
}
}
}
else
{
lean_dec(x_610);
return x_611;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_608;
}
}
}
else
{
lean_object* x_630; 
lean_dec_ref(x_24);
lean_del_object(x_9);
lean_inc_ref(x_4);
x_630 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
if (lean_obj_tag(x_631) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_630;
}
else
{
lean_object* x_632; lean_object* x_633; 
lean_dec_ref(x_630);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
lean_dec_ref(x_631);
x_633 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; 
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
if (lean_obj_tag(x_634) == 0)
{
lean_dec(x_632);
return x_633;
}
else
{
lean_object* x_635; uint8_t x_636; uint8_t x_650; 
x_650 = !lean_is_exclusive(x_633);
if (x_650 == 0)
{
lean_object* x_651; 
x_651 = lean_ctor_get(x_633, 0);
lean_dec(x_651);
x_635 = x_633;
x_636 = x_650;
goto block_649;
}
else
{
lean_dec(x_633);
x_635 = lean_box(0);
x_636 = x_650;
goto block_649;
}
block_649:
{
lean_object* x_637; lean_object* x_638; uint8_t x_639; uint8_t x_648; 
x_637 = lean_ctor_get(x_634, 0);
x_648 = !lean_is_exclusive(x_634);
if (x_648 == 0)
{
x_638 = x_634;
x_639 = x_648;
goto block_647;
}
else
{
lean_inc(x_637);
lean_dec(x_634);
x_638 = lean_box(0);
x_639 = x_648;
goto block_647;
}
block_647:
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_nat_div(x_632, x_637);
lean_dec(x_637);
lean_dec(x_632);
if (x_639 == 0)
{
lean_ctor_set(x_638, 0, x_640);
x_641 = x_638;
goto block_645;
}
else
{
lean_object* x_646; 
x_646 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_646, 0, x_640);
x_641 = x_646;
goto block_645;
}
block_645:
{
lean_object* x_642; 
if (x_636 == 0)
{
lean_ctor_set(x_635, 0, x_641);
x_642 = x_635;
goto block_643;
}
else
{
lean_object* x_644; 
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_641);
x_642 = x_644;
goto block_643;
}
block_643:
{
return x_642;
}
}
}
}
}
}
else
{
lean_dec(x_632);
return x_633;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_630;
}
}
}
else
{
lean_object* x_652; 
lean_dec_ref(x_24);
lean_del_object(x_9);
lean_inc_ref(x_4);
x_652 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
if (lean_obj_tag(x_653) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_652;
}
else
{
lean_object* x_654; lean_object* x_655; 
lean_dec_ref(x_652);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
lean_dec_ref(x_653);
x_655 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
if (lean_obj_tag(x_656) == 0)
{
lean_dec(x_654);
return x_655;
}
else
{
lean_object* x_657; uint8_t x_658; uint8_t x_672; 
x_672 = !lean_is_exclusive(x_655);
if (x_672 == 0)
{
lean_object* x_673; 
x_673 = lean_ctor_get(x_655, 0);
lean_dec(x_673);
x_657 = x_655;
x_658 = x_672;
goto block_671;
}
else
{
lean_dec(x_655);
x_657 = lean_box(0);
x_658 = x_672;
goto block_671;
}
block_671:
{
lean_object* x_659; lean_object* x_660; uint8_t x_661; uint8_t x_670; 
x_659 = lean_ctor_get(x_656, 0);
x_670 = !lean_is_exclusive(x_656);
if (x_670 == 0)
{
x_660 = x_656;
x_661 = x_670;
goto block_669;
}
else
{
lean_inc(x_659);
lean_dec(x_656);
x_660 = lean_box(0);
x_661 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_nat_mod(x_654, x_659);
lean_dec(x_659);
lean_dec(x_654);
if (x_661 == 0)
{
lean_ctor_set(x_660, 0, x_662);
x_663 = x_660;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_668, 0, x_662);
x_663 = x_668;
goto block_667;
}
block_667:
{
lean_object* x_664; 
if (x_658 == 0)
{
lean_ctor_set(x_657, 0, x_663);
x_664 = x_657;
goto block_665;
}
else
{
lean_object* x_666; 
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_663);
x_664 = x_666;
goto block_665;
}
block_665:
{
return x_664;
}
}
}
}
}
}
else
{
lean_dec(x_654);
return x_655;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_4);
return x_652;
}
}
}
else
{
lean_object* x_674; 
lean_dec_ref(x_24);
lean_del_object(x_9);
x_674 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(x_23, x_18, x_2, x_3, x_4, x_5);
return x_674;
}
}
}
else
{
lean_object* x_675; 
lean_dec_ref(x_19);
lean_del_object(x_9);
x_675 = l_Lean_Meta_evalNat(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
if (lean_obj_tag(x_676) == 0)
{
return x_675;
}
else
{
lean_object* x_677; uint8_t x_678; uint8_t x_693; 
x_693 = !lean_is_exclusive(x_675);
if (x_693 == 0)
{
lean_object* x_694; 
x_694 = lean_ctor_get(x_675, 0);
lean_dec(x_694);
x_677 = x_675;
x_678 = x_693;
goto block_692;
}
else
{
lean_dec(x_675);
x_677 = lean_box(0);
x_678 = x_693;
goto block_692;
}
block_692:
{
lean_object* x_679; lean_object* x_680; uint8_t x_681; uint8_t x_691; 
x_679 = lean_ctor_get(x_676, 0);
x_691 = !lean_is_exclusive(x_676);
if (x_691 == 0)
{
x_680 = x_676;
x_681 = x_691;
goto block_690;
}
else
{
lean_inc(x_679);
lean_dec(x_676);
x_680 = lean_box(0);
x_681 = x_691;
goto block_690;
}
block_690:
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_unsigned_to_nat(1u);
x_683 = lean_nat_add(x_679, x_682);
lean_dec(x_679);
if (x_681 == 0)
{
lean_ctor_set(x_680, 0, x_683);
x_684 = x_680;
goto block_688;
}
else
{
lean_object* x_689; 
x_689 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_689, 0, x_683);
x_684 = x_689;
goto block_688;
}
block_688:
{
lean_object* x_685; 
if (x_678 == 0)
{
lean_ctor_set(x_677, 0, x_684);
x_685 = x_677;
goto block_686;
}
else
{
lean_object* x_687; 
x_687 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_687, 0, x_684);
x_685 = x_687;
goto block_686;
}
block_686:
{
return x_685;
}
}
}
}
}
}
else
{
return x_675;
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_697; lean_object* x_698; uint8_t x_699; uint8_t x_704; 
lean_dec_ref(x_4);
x_697 = lean_ctor_get(x_7, 0);
x_704 = !lean_is_exclusive(x_7);
if (x_704 == 0)
{
x_698 = x_7;
x_699 = x_704;
goto block_703;
}
else
{
lean_inc(x_697);
lean_dec(x_7);
x_698 = lean_box(0);
x_699 = x_704;
goto block_703;
}
block_703:
{
lean_object* x_700; 
if (x_699 == 0)
{
x_700 = x_698;
goto block_701;
}
else
{
lean_object* x_702; 
x_702 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_702, 0, x_697);
x_700 = x_702;
goto block_701;
}
block_701:
{
return x_700;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 9:
{
lean_object* x_10; 
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
x_14 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_dec_ref(x_10);
goto block_9;
}
}
case 10:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_1 = x_20;
goto _start;
}
case 4:
{
lean_object* x_22; 
lean_dec_ref(x_4);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec_ref(x_1);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_22);
x_26 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_23);
x_27 = ((lean_object*)(l_Lean_Meta_evalNat___closed__0));
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec_ref(x_26);
if (x_28 == 0)
{
lean_dec_ref(x_25);
goto block_9;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l_Lean_Meta_evalNat___closed__1));
x_30 = lean_string_dec_eq(x_25, x_29);
lean_dec_ref(x_25);
if (x_30 == 0)
{
goto block_9;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l_Lean_Meta_evalNat___closed__2));
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
goto block_9;
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_23);
goto block_9;
}
}
else
{
lean_dec(x_22);
goto block_9;
}
}
case 5:
{
lean_object* x_33; 
x_33 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5);
return x_33;
}
case 2:
{
lean_object* x_34; 
x_34 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5);
return x_34;
}
default: 
{
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_5);
x_8 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
lean_inc_ref(x_5);
lean_inc(x_10);
x_12 = l_Lean_checkExponent(x_10, x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_41; 
x_13 = lean_ctor_get(x_12, 0);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
x_14 = x_12;
x_15 = x_41;
goto block_40;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_16; 
x_16 = lean_unbox(x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_17 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; 
lean_del_object(x_14);
x_21 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_10);
return x_21;
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_21, 0);
lean_dec(x_39);
x_23 = x_21;
x_24 = x_38;
goto block_37;
}
else
{
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_36; 
x_25 = lean_ctor_get(x_22, 0);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
x_26 = x_22;
x_27 = x_36;
goto block_35;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_nat_pow(x_25, x_10);
lean_dec(x_10);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_28);
x_29 = x_26;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_29);
x_30 = x_23;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
else
{
lean_dec(x_10);
return x_21;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_12, 0);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
x_43 = x_12;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_12);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 0);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
x_10 = x_8;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_8, 0);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
x_18 = x_8;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_66; 
x_9 = l_Lean_Meta_Context_config(x_4);
x_10 = lean_ctor_get_uint8(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, 2);
x_13 = lean_ctor_get_uint8(x_9, 3);
x_14 = lean_ctor_get_uint8(x_9, 4);
x_15 = lean_ctor_get_uint8(x_9, 5);
x_16 = lean_ctor_get_uint8(x_9, 6);
x_17 = lean_ctor_get_uint8(x_9, 7);
x_18 = lean_ctor_get_uint8(x_9, 8);
x_19 = lean_ctor_get_uint8(x_9, 10);
x_20 = lean_ctor_get_uint8(x_9, 11);
x_21 = lean_ctor_get_uint8(x_9, 12);
x_22 = lean_ctor_get_uint8(x_9, 13);
x_23 = lean_ctor_get_uint8(x_9, 14);
x_24 = lean_ctor_get_uint8(x_9, 15);
x_25 = lean_ctor_get_uint8(x_9, 16);
x_26 = lean_ctor_get_uint8(x_9, 17);
x_27 = lean_ctor_get_uint8(x_9, 18);
x_66 = !lean_is_exclusive(x_9);
if (x_66 == 0)
{
x_28 = x_9;
x_29 = x_66;
goto block_65;
}
else
{
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_30 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_4, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 6);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_38 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_39 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 3);
if (x_29 == 0)
{
x_40 = x_28;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_64, 0, x_10);
lean_ctor_set_uint8(x_64, 1, x_11);
lean_ctor_set_uint8(x_64, 2, x_12);
lean_ctor_set_uint8(x_64, 3, x_13);
lean_ctor_set_uint8(x_64, 4, x_14);
lean_ctor_set_uint8(x_64, 5, x_15);
lean_ctor_set_uint8(x_64, 6, x_16);
lean_ctor_set_uint8(x_64, 7, x_17);
lean_ctor_set_uint8(x_64, 8, x_18);
lean_ctor_set_uint8(x_64, 10, x_19);
lean_ctor_set_uint8(x_64, 11, x_20);
lean_ctor_set_uint8(x_64, 12, x_21);
lean_ctor_set_uint8(x_64, 13, x_22);
lean_ctor_set_uint8(x_64, 14, x_23);
lean_ctor_set_uint8(x_64, 15, x_24);
lean_ctor_set_uint8(x_64, 16, x_25);
lean_ctor_set_uint8(x_64, 17, x_26);
lean_ctor_set_uint8(x_64, 18, x_27);
x_40 = x_64;
goto block_63;
}
block_63:
{
uint64_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_55; 
lean_ctor_set_uint8(x_40, 9, x_1);
x_41 = l_Lean_Meta_Context_configKey(x_4);
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_4, 6);
lean_dec(x_56);
x_57 = lean_ctor_get(x_4, 5);
lean_dec(x_57);
x_58 = lean_ctor_get(x_4, 4);
lean_dec(x_58);
x_59 = lean_ctor_get(x_4, 3);
lean_dec(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_4, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_4, 0);
lean_dec(x_62);
x_42 = x_4;
x_43 = x_55;
goto block_54;
}
else
{
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = x_55;
goto block_54;
}
block_54:
{
uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; 
x_44 = 2;
x_45 = lean_uint64_shift_right(x_41, x_44);
x_46 = lean_uint64_shift_left(x_45, x_44);
x_47 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_48 = lean_uint64_lor(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_48);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_49);
x_50 = x_42;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_31);
lean_ctor_set(x_53, 2, x_32);
lean_ctor_set(x_53, 3, x_33);
lean_ctor_set(x_53, 4, x_34);
lean_ctor_set(x_53, 5, x_35);
lean_ctor_set(x_53, 6, x_36);
lean_ctor_set_uint8(x_53, sizeof(void*)*7, x_30);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 1, x_37);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 2, x_38);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 3, x_39);
x_50 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_51; 
x_51 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_50, x_5, x_6, x_7);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Meta_matchesInstance___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = 3;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_matchesInstance___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
x_11 = 0;
x_12 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(x_10, x_11, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_matchesInstance(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_169; 
x_8 = lean_ctor_get(x_7, 0);
x_169 = !lean_is_exclusive(x_7);
if (x_169 == 0)
{
x_9 = x_7;
x_10 = x_169;
goto block_168;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_8);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1));
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isApp(x_19);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_23);
x_83 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_84 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13));
x_85 = l_Lean_Expr_isConstOf(x_83, x_84);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Expr_isApp(x_83);
if (x_86 == 0)
{
lean_dec_ref(x_83);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc_ref(x_87);
x_88 = l_Lean_Expr_appFnCleanup___redArg(x_83);
x_89 = l_Lean_Expr_isApp(x_88);
if (x_89 == 0)
{
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = l_Lean_Expr_appFnCleanup___redArg(x_88);
x_91 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28));
x_92 = l_Lean_Expr_isConstOf(x_90, x_91);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Expr_isApp(x_90);
if (x_93 == 0)
{
lean_dec_ref(x_90);
lean_dec_ref(x_87);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = l_Lean_Expr_appFnCleanup___redArg(x_90);
x_95 = l_Lean_Expr_isApp(x_94);
if (x_95 == 0)
{
lean_dec_ref(x_94);
lean_dec_ref(x_87);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = l_Lean_Expr_appFnCleanup___redArg(x_94);
x_97 = ((lean_object*)(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48));
x_98 = l_Lean_Expr_isConstOf(x_96, x_97);
lean_dec_ref(x_96);
if (x_98 == 0)
{
lean_dec_ref(x_87);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_del_object(x_9);
x_99 = l_Lean_Nat_mkInstHAdd;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_100 = l_Lean_Meta_matchesInstance(x_87, x_99, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_110; 
x_101 = lean_ctor_get(x_100, 0);
x_110 = !lean_is_exclusive(x_100);
if (x_110 == 0)
{
x_102 = x_100;
x_103 = x_110;
goto block_109;
}
else
{
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = x_110;
goto block_109;
}
block_109:
{
uint8_t x_104; 
x_104 = lean_unbox(x_101);
lean_dec(x_101);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = lean_box(0);
if (x_103 == 0)
{
lean_ctor_set(x_102, 0, x_105);
x_106 = x_102;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
else
{
lean_del_object(x_102);
x_24 = x_18;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
goto block_82;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_111 = lean_ctor_get(x_100, 0);
x_118 = !lean_is_exclusive(x_100);
if (x_118 == 0)
{
x_112 = x_100;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_90);
lean_del_object(x_9);
x_119 = l_Lean_Nat_mkInstAdd;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_120 = l_Lean_Meta_matchesInstance(x_87, x_119, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_130; 
x_121 = lean_ctor_get(x_120, 0);
x_130 = !lean_is_exclusive(x_120);
if (x_130 == 0)
{
x_122 = x_120;
x_123 = x_130;
goto block_129;
}
else
{
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = x_130;
goto block_129;
}
block_129:
{
uint8_t x_124; 
x_124 = lean_unbox(x_121);
lean_dec(x_121);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_125 = lean_box(0);
if (x_123 == 0)
{
lean_ctor_set(x_122, 0, x_125);
x_126 = x_122;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
else
{
lean_del_object(x_122);
x_24 = x_18;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
goto block_82;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_138; 
lean_dec_ref(x_23);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_131 = lean_ctor_get(x_120, 0);
x_138 = !lean_is_exclusive(x_120);
if (x_138 == 0)
{
x_132 = x_120;
x_133 = x_138;
goto block_137;
}
else
{
lean_inc(x_131);
lean_dec(x_120);
x_132 = lean_box(0);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_133 == 0)
{
x_134 = x_132;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_131);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_83);
lean_del_object(x_9);
x_24 = x_18;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
goto block_82;
}
block_82:
{
lean_object* x_29; 
lean_inc_ref(x_27);
x_29 = l_Lean_Meta_evalNat(x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_73; 
x_30 = lean_ctor_get(x_29, 0);
x_73 = !lean_is_exclusive(x_29);
if (x_73 == 0)
{
x_31 = x_29;
x_32 = x_73;
goto block_72;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_73;
goto block_72;
}
block_72:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_23);
x_33 = lean_box(0);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_33);
x_34 = x_31;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_71; 
lean_del_object(x_31);
x_37 = lean_ctor_get(x_30, 0);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
x_38 = x_30;
x_39 = x_71;
goto block_70;
}
else
{
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_40; 
x_40 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_23, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_61; 
x_41 = lean_ctor_get(x_40, 0);
x_61 = !lean_is_exclusive(x_40);
if (x_61 == 0)
{
x_42 = x_40;
x_43 = x_61;
goto block_60;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_59; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
x_46 = x_41;
x_47 = x_59;
goto block_58;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_nat_add(x_45, x_37);
lean_dec(x_37);
lean_dec(x_45);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_48);
x_49 = x_46;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_48);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; 
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_49);
x_50 = x_38;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_50);
x_51 = x_42;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_38);
lean_dec(x_37);
x_62 = lean_ctor_get(x_40, 0);
x_69 = !lean_is_exclusive(x_40);
if (x_69 == 0)
{
x_63 = x_40;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_40);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_23);
x_74 = lean_ctor_get(x_29, 0);
x_81 = !lean_is_exclusive(x_29);
if (x_81 == 0)
{
x_75 = x_29;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_29);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
}
else
{
lean_object* x_139; 
lean_dec_ref(x_19);
lean_del_object(x_9);
x_139 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_159; 
x_140 = lean_ctor_get(x_139, 0);
x_159 = !lean_is_exclusive(x_139);
if (x_159 == 0)
{
x_141 = x_139;
x_142 = x_159;
goto block_158;
}
else
{
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_box(0);
x_142 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_157; 
x_143 = lean_ctor_get(x_140, 0);
x_144 = lean_ctor_get(x_140, 1);
x_157 = !lean_is_exclusive(x_140);
if (x_157 == 0)
{
x_145 = x_140;
x_146 = x_157;
goto block_156;
}
else
{
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_140);
x_145 = lean_box(0);
x_146 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_add(x_144, x_147);
lean_dec(x_144);
if (x_146 == 0)
{
lean_ctor_set(x_145, 1, x_148);
x_149 = x_145;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_148);
x_149 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
if (x_142 == 0)
{
lean_ctor_set(x_141, 0, x_150);
x_151 = x_141;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_167; 
x_160 = lean_ctor_get(x_139, 0);
x_167 = !lean_is_exclusive(x_139);
if (x_167 == 0)
{
x_161 = x_139;
x_162 = x_167;
goto block_166;
}
else
{
lean_inc(x_160);
lean_dec(x_139);
x_161 = lean_box(0);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_162 == 0)
{
x_163 = x_161;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_160);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_170 = lean_ctor_get(x_7, 0);
x_177 = !lean_is_exclusive(x_7);
if (x_177 == 0)
{
x_171 = x_7;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_dec(x_7);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_21; 
x_8 = lean_ctor_get(x_7, 0);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
x_9 = x_7;
x_10 = x_21;
goto block_20;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_21;
goto block_20;
}
block_20:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_12);
x_13 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_16);
x_17 = x_9;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_7, 0);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
x_23 = x_7;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_24; 
x_8 = lean_ctor_get(x_7, 0);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
x_9 = x_7;
x_10 = x_24;
goto block_23;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_24;
goto block_23;
}
block_23:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
x_14 = lean_box(x_13);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_14);
x_15 = x_9;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_18 = 0;
x_19 = lean_box(x_18);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_19);
x_20 = x_9;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_7, 0);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_26 = x_7;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc_ref(x_1);
x_10 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_25; 
x_11 = lean_ctor_get(x_10, 0);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
x_12 = x_10;
x_13 = x_25;
goto block_24;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_25;
goto block_24;
}
block_24:
{
uint8_t x_14; 
x_14 = lean_unbox(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_mkNatLit(x_2);
x_16 = l_Lean_mkNatAdd(x_1, x_15);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_16);
x_17 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_20 = l_Lean_mkNatLit(x_2);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_20);
x_21 = x_12;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_10, 0);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
x_27 = x_10;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_1);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
x_9 = lean_ctor_get(x_8, 0);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
x_10 = x_8;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = l_Bool_toLBool(x_12);
x_14 = lean_box(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_20 = lean_ctor_get(x_8, 0);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
x_21 = x_8;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Meta_isDefEqOffset___lam__1(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__0));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_56; 
x_56 = l_Lean_Meta_getConfig___redArg(x_3);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_202; 
x_57 = lean_ctor_get(x_56, 0);
x_202 = !lean_is_exclusive(x_56);
if (x_202 == 0)
{
x_58 = x_56;
x_59 = x_202;
goto block_201;
}
else
{
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = x_202;
goto block_201;
}
block_201:
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_57, 8);
lean_dec(x_57);
if (x_60 == 0)
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = 2;
x_62 = lean_box(x_61);
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_62);
x_63 = x_58;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; 
lean_del_object(x_58);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_66 = l_Lean_Meta_isOffset_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_120; 
x_69 = lean_ctor_get(x_68, 0);
x_120 = !lean_is_exclusive(x_68);
if (x_120 == 0)
{
x_70 = x_68;
x_71 = x_120;
goto block_119;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_120;
goto block_119;
}
block_119:
{
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = 2;
x_73 = lean_box(x_72);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_73);
x_74 = x_70;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_del_object(x_70);
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec_ref(x_69);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_78 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_inc_ref(x_5);
x_80 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_95; 
x_81 = lean_ctor_get(x_80, 0);
x_95 = !lean_is_exclusive(x_80);
if (x_95 == 0)
{
x_82 = x_80;
x_83 = x_95;
goto block_94;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_95;
goto block_94;
}
block_94:
{
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_84 = 2;
x_85 = lean_box(x_84);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_85);
x_86 = x_82;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
else
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_del_object(x_82);
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec_ref(x_81);
x_90 = lean_nat_dec_eq(x_77, x_89);
lean_dec(x_89);
lean_dec(x_77);
x_91 = l_Bool_toLBool(x_90);
x_92 = lean_box(x_91);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__1___boxed), 6, 1);
lean_closure_set(x_93, 0, x_92);
x_8 = x_93;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
goto block_47;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_96 = lean_ctor_get(x_80, 0);
x_103 = !lean_is_exclusive(x_80);
if (x_103 == 0)
{
x_97 = x_80;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_80);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec_ref(x_2);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
lean_dec_ref(x_79);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_nat_dec_le(x_106, x_77);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_77);
x_108 = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
x_8 = x_108;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
goto block_47;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_nat_sub(x_77, x_106);
lean_dec(x_106);
lean_dec(x_77);
x_110 = l_Lean_mkNatLit(x_109);
x_48 = x_110;
x_49 = x_105;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
goto block_55;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_78, 0);
x_118 = !lean_is_exclusive(x_78);
if (x_118 == 0)
{
x_112 = x_78;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_78);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_68, 0);
x_128 = !lean_is_exclusive(x_68);
if (x_128 == 0)
{
x_122 = x_68;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_68);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_67, 0);
lean_inc(x_129);
lean_dec_ref(x_67);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_132 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
lean_inc_ref(x_5);
x_134 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_149; 
x_135 = lean_ctor_get(x_134, 0);
x_149 = !lean_is_exclusive(x_134);
if (x_149 == 0)
{
x_136 = x_134;
x_137 = x_149;
goto block_148;
}
else
{
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_box(0);
x_137 = x_149;
goto block_148;
}
block_148:
{
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_138 = 2;
x_139 = lean_box(x_138);
if (x_137 == 0)
{
lean_ctor_set(x_136, 0, x_139);
x_140 = x_136;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_139);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
else
{
lean_object* x_143; uint8_t x_144; 
lean_del_object(x_136);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
lean_dec_ref(x_135);
x_144 = lean_nat_dec_le(x_131, x_143);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_143);
lean_dec(x_131);
lean_dec(x_130);
x_145 = ((lean_object*)(l_Lean_Meta_isDefEqOffset___closed__2));
x_8 = x_145;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
goto block_47;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_nat_sub(x_143, x_131);
lean_dec(x_131);
lean_dec(x_143);
x_147 = l_Lean_mkNatLit(x_146);
x_48 = x_130;
x_49 = x_147;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
goto block_55;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_157; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_134, 0);
x_157 = !lean_is_exclusive(x_134);
if (x_157 == 0)
{
x_151 = x_134;
x_152 = x_157;
goto block_156;
}
else
{
lean_inc(x_150);
lean_dec(x_134);
x_151 = lean_box(0);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_152 == 0)
{
x_153 = x_151;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_150);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec_ref(x_2);
x_158 = lean_ctor_get(x_133, 0);
lean_inc(x_158);
lean_dec_ref(x_133);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_nat_dec_eq(x_131, x_160);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = lean_nat_dec_lt(x_131, x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_nat_sub(x_131, x_160);
lean_dec(x_160);
lean_dec(x_131);
lean_inc_ref(x_5);
x_164 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_130, x_163, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_48 = x_165;
x_49 = x_159;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
goto block_55;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_173; 
lean_dec(x_159);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_164, 0);
x_173 = !lean_is_exclusive(x_164);
if (x_173 == 0)
{
x_167 = x_164;
x_168 = x_173;
goto block_172;
}
else
{
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_box(0);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_168 == 0)
{
x_169 = x_167;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_166);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_nat_sub(x_160, x_131);
lean_dec(x_131);
lean_dec(x_160);
lean_inc_ref(x_5);
x_175 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_159, x_174, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_48 = x_130;
x_49 = x_176;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
goto block_55;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_184; 
lean_dec(x_130);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_175, 0);
x_184 = !lean_is_exclusive(x_175);
if (x_184 == 0)
{
x_178 = x_175;
x_179 = x_184;
goto block_183;
}
else
{
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_box(0);
x_179 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_180; 
if (x_179 == 0)
{
x_180 = x_178;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_177);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
}
else
{
lean_dec(x_160);
lean_dec(x_131);
x_48 = x_130;
x_49 = x_159;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
goto block_55;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_192; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_132, 0);
x_192 = !lean_is_exclusive(x_132);
if (x_192 == 0)
{
x_186 = x_132;
x_187 = x_192;
goto block_191;
}
else
{
lean_inc(x_185);
lean_dec(x_132);
x_186 = lean_box(0);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_187 == 0)
{
x_188 = x_186;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_185);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_200; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_193 = lean_ctor_get(x_66, 0);
x_200 = !lean_is_exclusive(x_66);
if (x_200 == 0)
{
x_194 = x_66;
x_195 = x_200;
goto block_199;
}
else
{
lean_inc(x_193);
lean_dec(x_66);
x_194 = lean_box(0);
x_195 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_196; 
if (x_195 == 0)
{
x_196 = x_194;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_193);
x_196 = x_198;
goto block_197;
}
block_197:
{
return x_196;
}
}
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_210; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_203 = lean_ctor_get(x_56, 0);
x_210 = !lean_is_exclusive(x_56);
if (x_210 == 0)
{
x_204 = x_56;
x_205 = x_210;
goto block_209;
}
else
{
lean_inc(x_203);
lean_dec(x_56);
x_204 = lean_box(0);
x_205 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_206; 
if (x_205 == 0)
{
x_206 = x_204;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_203);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
}
block_47:
{
lean_object* x_13; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_13 = lean_infer_type(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_obj_once(&l_Lean_Meta_isDefEqOffset___closed__1, &l_Lean_Meta_isDefEqOffset___closed__1_once, _init_l_Lean_Meta_isDefEqOffset___closed__1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_18 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(x_16, x_17, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_30; 
x_19 = lean_ctor_get(x_18, 0);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
x_20 = x_18;
x_21 = x_30;
goto block_29;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_22; 
x_22 = lean_unbox(x_19);
lean_dec(x_19);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_23 = 2;
x_24 = lean_box(x_23);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_24);
x_25 = x_20;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; 
lean_del_object(x_20);
x_28 = lean_apply_5(x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_28;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_31 = lean_ctor_get(x_18, 0);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_39 = lean_ctor_get(x_13, 0);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
x_40 = x_13;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
block_55:
{
lean_object* x_54; 
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__0___boxed), 7, 2);
lean_closure_set(x_54, 0, x_48);
lean_closure_set(x_54, 1, x_49);
x_8 = x_54;
x_9 = x_50;
x_10 = x_51;
x_11 = x_52;
x_12 = x_53;
goto block_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isDefEqOffset(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
res = runtime_initialize_Lean_Data_LBool(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin)
;
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
res = initialize_Lean_Data_LBool(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Offset(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Offset(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Offset(builtin);
}
#ifdef __cplusplus
}
#endif
