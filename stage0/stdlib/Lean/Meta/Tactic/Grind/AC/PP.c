// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.PP
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.AC.DenoteExpr import Init.Omega
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
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(lean_object*, lean_object*);
static const lean_array_object l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basis"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "basis"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 84, 4, 167, 160, 107, 84, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Disequalities"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "diseqs"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 198, 81, 139, 128, 228, 160, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Operator `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Properties"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "assoc"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 39, 65, 244, 27, 146, 241, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "properties"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(15, 175, 253, 162, 13, 144, 103, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "identity: `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "idempotent"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commutative"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_pp_x3f___closed__0;
static const lean_string_object l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Operators"};
static const lean_object* l_Lean_Meta_Grind_AC_pp_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_AC_pp_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_pp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0);
v___x_3_ = l_ReaderT_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM(void){
_start:
{
lean_object* v___x_8_; lean_object* v_toApplicative_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_67_; 
v___x_8_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1);
v_toApplicative_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v___x_8_, 1);
lean_dec(v_unused_68_);
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_67_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_toApplicative_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_67_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v_toFunctor_13_; lean_object* v_toSeq_14_; lean_object* v_toSeqLeft_15_; lean_object* v_toSeqRight_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_65_; 
v_toFunctor_13_ = lean_ctor_get(v_toApplicative_9_, 0);
v_toSeq_14_ = lean_ctor_get(v_toApplicative_9_, 2);
v_toSeqLeft_15_ = lean_ctor_get(v_toApplicative_9_, 3);
v_toSeqRight_16_ = lean_ctor_get(v_toApplicative_9_, 4);
v_isSharedCheck_65_ = !lean_is_exclusive(v_toApplicative_9_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v_toApplicative_9_, 1);
lean_dec(v_unused_66_);
v___x_18_ = v_toApplicative_9_;
v_isShared_19_ = v_isSharedCheck_65_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_toSeqRight_16_);
lean_inc(v_toSeqLeft_15_);
lean_inc(v_toSeq_14_);
lean_inc(v_toFunctor_13_);
lean_dec(v_toApplicative_9_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_65_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_29_; 
v___f_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2));
v___f_21_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3));
lean_inc_ref(v_toFunctor_13_);
v___f_22_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_22_, 0, v_toFunctor_13_);
v___f_23_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_23_, 0, v_toFunctor_13_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___f_22_);
lean_ctor_set(v___x_24_, 1, v___f_23_);
v___f_25_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_25_, 0, v_toSeqRight_16_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_26_, 0, v_toSeqLeft_15_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_27_, 0, v_toSeq_14_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___f_25_);
lean_ctor_set(v___x_18_, 3, v___f_26_);
lean_ctor_set(v___x_18_, 2, v___f_27_);
lean_ctor_set(v___x_18_, 1, v___f_20_);
lean_ctor_set(v___x_18_, 0, v___x_24_);
v___x_29_ = v___x_18_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___f_20_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v___f_27_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v___f_26_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v___f_25_);
v___x_29_ = v_reuseFailAlloc_64_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_31_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___f_21_);
lean_ctor_set(v___x_11_, 0, v___x_29_);
v___x_31_ = v___x_11_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___f_21_);
v___x_31_ = v_reuseFailAlloc_63_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; lean_object* v_toApplicative_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_61_; 
v___x_32_ = l_ReaderT_instMonad___redArg(v___x_31_);
v_toApplicative_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v___x_32_, 1);
lean_dec(v_unused_62_);
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_61_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_toApplicative_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_61_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v_toFunctor_37_; lean_object* v_toSeq_38_; lean_object* v_toSeqLeft_39_; lean_object* v_toSeqRight_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_59_; 
v_toFunctor_37_ = lean_ctor_get(v_toApplicative_33_, 0);
v_toSeq_38_ = lean_ctor_get(v_toApplicative_33_, 2);
v_toSeqLeft_39_ = lean_ctor_get(v_toApplicative_33_, 3);
v_toSeqRight_40_ = lean_ctor_get(v_toApplicative_33_, 4);
v_isSharedCheck_59_ = !lean_is_exclusive(v_toApplicative_33_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v_toApplicative_33_, 1);
lean_dec(v_unused_60_);
v___x_42_ = v_toApplicative_33_;
v_isShared_43_ = v_isSharedCheck_59_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toSeqRight_40_);
lean_inc(v_toSeqLeft_39_);
lean_inc(v_toSeq_38_);
lean_inc(v_toFunctor_37_);
lean_dec(v_toApplicative_33_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_59_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___x_53_; 
v___f_44_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4));
v___f_45_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5));
lean_inc_ref(v_toFunctor_37_);
v___f_46_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_46_, 0, v_toFunctor_37_);
v___f_47_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_47_, 0, v_toFunctor_37_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___f_46_);
lean_ctor_set(v___x_48_, 1, v___f_47_);
v___f_49_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_49_, 0, v_toSeqRight_40_);
v___f_50_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_50_, 0, v_toSeqLeft_39_);
v___f_51_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_51_, 0, v_toSeq_38_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 4, v___f_49_);
lean_ctor_set(v___x_42_, 3, v___f_50_);
lean_ctor_set(v___x_42_, 2, v___f_51_);
lean_ctor_set(v___x_42_, 1, v___f_44_);
lean_ctor_set(v___x_42_, 0, v___x_48_);
v___x_53_ = v___x_42_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___f_44_);
lean_ctor_set(v_reuseFailAlloc_58_, 2, v___f_51_);
lean_ctor_set(v_reuseFailAlloc_58_, 3, v___f_50_);
lean_ctor_set(v_reuseFailAlloc_58_, 4, v___f_49_);
v___x_53_ = v_reuseFailAlloc_58_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_55_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___f_45_);
lean_ctor_set(v___x_35_, 0, v___x_53_);
v___x_55_ = v___x_35_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___f_45_);
v___x_55_ = v_reuseFailAlloc_57_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; 
v___x_56_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_56_, 0, lean_box(0));
lean_closure_set(v___x_56_, 1, lean_box(0));
lean_closure_set(v___x_56_, 2, v___x_55_);
return v___x_56_;
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
static double _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0(void){
_start:
{
lean_object* v___x_69_; double v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_float_of_nat(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(lean_object* v_cls_72_, lean_object* v_header_73_, lean_object* v_msgs_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_array_get_size(v_msgs_74_);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; lean_object* v___x_79_; double v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_78_ = 1;
v___x_79_ = lean_box(0);
v___x_80_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_82_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_82_, 0, v_cls_72_);
lean_ctor_set(v___x_82_, 1, v___x_79_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set_float(v___x_82_, sizeof(void*)*3, v___x_80_);
lean_ctor_set_float(v___x_82_, sizeof(void*)*3 + 8, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*3 + 16, v___x_78_);
v___x_83_ = lean_thunk_get_own(v_header_73_);
v___x_84_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
lean_ctor_set(v___x_84_, 2, v_msgs_74_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v_msgs_74_);
lean_dec(v_cls_72_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___boxed(lean_object* v_cls_87_, lean_object* v_header_88_, lean_object* v_msgs_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v_cls_87_, v_header_88_, v_msgs_89_);
lean_dec_ref(v_header_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(lean_object* v_msgs_91_, lean_object* v_msg_x3f_92_){
_start:
{
if (lean_obj_tag(v_msg_x3f_92_) == 1)
{
lean_object* v_val_93_; lean_object* v___x_94_; 
v_val_93_ = lean_ctor_get(v_msg_x3f_92_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v_msg_x3f_92_);
v___x_94_ = lean_array_push(v_msgs_91_, v_val_93_);
return v___x_94_;
}
else
{
lean_dec(v_msg_x3f_92_);
return v_msgs_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(lean_object* v_e_97_, lean_object* v_cls_98_){
_start:
{
lean_object* v___x_99_; double v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_99_ = lean_box(0);
v___x_100_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_101_ = 1;
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_103_, 0, v_cls_98_);
lean_ctor_set(v___x_103_, 1, v___x_99_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3, v___x_100_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3 + 8, v___x_100_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 16, v___x_101_);
v___x_104_ = l_Lean_MessageData_ofExpr(v_e_97_);
v___x_105_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_103_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1));
v___x_111_ = l_Lean_MessageData_ofFormat(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0(lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(lean_object* v_s_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_s_114_) == 0)
{
lean_object* v_vars_118_; lean_object* v_x_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_135_; 
v_vars_118_ = lean_ctor_get(v___y_115_, 10);
v_x_119_ = lean_ctor_get(v_s_114_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_s_114_);
if (v_isSharedCheck_135_ == 0)
{
v___x_121_ = v_s_114_;
v_isShared_122_ = v_isSharedCheck_135_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_x_119_);
lean_dec(v_s_114_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_135_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_size_123_; uint8_t v___x_124_; 
v_size_123_ = lean_ctor_get(v_vars_118_, 2);
v___x_124_ = lean_nat_dec_lt(v_x_119_, v_size_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_x_119_);
v___x_125_ = l_outOfBounds___redArg(v___x_117_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___y_115_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_126_);
v___x_128_ = v___x_121_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_inc_ref(v_vars_118_);
v___x_130_ = l_Lean_PersistentArray_get_x21___redArg(v___x_117_, v_vars_118_, v_x_119_);
lean_dec(v_x_119_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___y_115_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_131_);
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_object* v_x_136_; lean_object* v_s_137_; lean_object* v___x_138_; lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_164_; 
v_x_136_ = lean_ctor_get(v_s_114_, 0);
lean_inc(v_x_136_);
v_s_137_ = lean_ctor_get(v_s_114_, 1);
lean_inc_ref(v_s_137_);
lean_dec_ref(v_s_114_);
lean_inc_ref(v___y_115_);
v___x_138_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_137_, v___y_115_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_164_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_164_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_164_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_163_; 
v_fst_143_ = lean_ctor_get(v_a_139_, 0);
v_snd_144_ = lean_ctor_get(v_a_139_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_163_ == 0)
{
v___x_146_ = v_a_139_;
v_isShared_147_ = v_isSharedCheck_163_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snd_144_);
lean_inc(v_fst_143_);
lean_dec(v_a_139_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_163_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_op_148_; lean_object* v_vars_149_; lean_object* v___y_151_; lean_object* v_size_159_; uint8_t v___x_160_; 
v_op_148_ = lean_ctor_get(v___y_115_, 3);
lean_inc_ref(v_op_148_);
v_vars_149_ = lean_ctor_get(v___y_115_, 10);
lean_inc_ref(v_vars_149_);
lean_dec_ref(v___y_115_);
v_size_159_ = lean_ctor_get(v_vars_149_, 2);
v___x_160_ = lean_nat_dec_lt(v_x_136_, v_size_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v_vars_149_);
lean_dec(v_x_136_);
v___x_161_ = l_outOfBounds___redArg(v___x_117_);
v___y_151_ = v___x_161_;
goto v___jp_150_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_PersistentArray_get_x21___redArg(v___x_117_, v_vars_149_, v_x_136_);
lean_dec(v_x_136_);
v___y_151_ = v___x_162_;
goto v___jp_150_;
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = l_Lean_mkAppB(v_op_148_, v___y_151_, v_fst_143_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_152_);
v___x_154_ = v___x_146_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_snd_144_);
v___x_154_ = v_reuseFailAlloc_158_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_156_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_154_);
v___x_156_ = v___x_141_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_s_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_165_, v___y_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(lean_object* v_c_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_lhs_179_; lean_object* v_rhs_180_; lean_object* v___x_181_; lean_object* v_a_182_; lean_object* v_fst_183_; lean_object* v_snd_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_215_; 
v_lhs_179_ = lean_ctor_get(v_c_172_, 0);
lean_inc_ref(v_lhs_179_);
v_rhs_180_ = lean_ctor_get(v_c_172_, 1);
lean_inc_ref(v_rhs_180_);
lean_dec_ref(v_c_172_);
lean_inc_ref(v___y_173_);
v___x_181_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_179_, v___y_173_);
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref(v___x_181_);
v_fst_183_ = lean_ctor_get(v_a_182_, 0);
v_snd_184_ = lean_ctor_get(v_a_182_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_a_182_);
if (v_isSharedCheck_215_ == 0)
{
v___x_186_ = v_a_182_;
v_isShared_187_ = v_isSharedCheck_215_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snd_184_);
lean_inc(v_fst_183_);
lean_dec(v_a_182_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_215_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_214_; 
v___x_188_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_180_, v_snd_184_);
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_214_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_214_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_214_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_213_; 
v_fst_193_ = lean_ctor_get(v_a_189_, 0);
v_snd_194_ = lean_ctor_get(v_a_189_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_a_189_);
if (v_isSharedCheck_213_ == 0)
{
v___x_196_ = v_a_189_;
v_isShared_197_ = v_isSharedCheck_213_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_snd_194_);
lean_inc(v_fst_193_);
lean_dec(v_a_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_213_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_type_198_; lean_object* v_u_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v_type_198_ = lean_ctor_get(v___y_173_, 1);
lean_inc_ref(v_type_198_);
v_u_199_ = lean_ctor_get(v___y_173_, 2);
lean_inc(v_u_199_);
lean_dec_ref(v___y_173_);
v___x_200_ = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1));
v___x_201_ = lean_box(0);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 1, v___x_201_);
lean_ctor_set(v___x_186_, 0, v_u_199_);
v___x_203_ = v___x_186_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_u_199_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_212_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_204_ = l_Lean_mkConst(v___x_200_, v___x_203_);
v___x_205_ = l_Lean_mkApp3(v___x_204_, v_type_198_, v_fst_183_, v_fst_193_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_205_);
v___x_207_ = v___x_196_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_snd_194_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_207_);
v___x_209_ = v___x_191_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___boxed(lean_object* v_c_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(lean_object* v_as_x27_228_, lean_object* v_b_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
if (lean_obj_tag(v_as_x27_228_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_b_229_);
lean_ctor_set(v___x_236_, 1, v___y_230_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v_head_238_; lean_object* v_tail_239_; lean_object* v___x_240_; lean_object* v_a_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_head_238_ = lean_ctor_get(v_as_x27_228_, 0);
lean_inc(v_head_238_);
v_tail_239_ = lean_ctor_get(v_as_x27_228_, 1);
lean_inc(v_tail_239_);
lean_dec_ref(v_as_x27_228_);
v___x_240_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_head_238_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref(v___x_240_);
v_fst_242_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_fst_242_);
v_snd_243_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_snd_243_);
lean_dec(v_a_241_);
v___x_244_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_245_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_242_, v___x_244_);
v___x_246_ = lean_array_push(v_b_229_, v___x_245_);
v_as_x27_228_ = v_tail_239_;
v_b_229_ = v___x_246_;
v___y_230_ = v_snd_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___boxed(lean_object* v_as_x27_248_, lean_object* v_b_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_248_, v_b_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3(void){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; 
v___f_261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0));
v___x_262_ = lean_mk_thunk(v___f_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_basis_269_; lean_object* v_basis_270_; lean_object* v___x_271_; 
v_basis_269_ = lean_ctor_get(v_a_263_, 15);
lean_inc(v_basis_269_);
v_basis_270_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_271_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_basis_269_, v_basis_270_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_291_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_291_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_291_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_291_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v_fst_276_; lean_object* v_snd_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_290_; 
v_fst_276_ = lean_ctor_get(v_a_272_, 0);
v_snd_277_ = lean_ctor_get(v_a_272_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v_a_272_);
if (v_isSharedCheck_290_ == 0)
{
v___x_279_ = v_a_272_;
v_isShared_280_ = v_isSharedCheck_290_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_snd_277_);
lean_inc(v_fst_276_);
lean_dec(v_a_272_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_290_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2));
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3);
v___x_283_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_281_, v___x_282_, v_fst_276_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_283_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_snd_277_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_285_);
v___x_287_ = v___x_274_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_a_292_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_271_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_271_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___boxed(lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(lean_object* v_as_307_, lean_object* v_as_x27_308_, lean_object* v_b_309_, lean_object* v_a_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_308_, v_b_309_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(lean_object* v_as_318_, lean_object* v_as_x27_319_, lean_object* v_b_320_, lean_object* v_a_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_318_, v_as_x27_319_, v_b_320_, v_a_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_as_318_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(lean_object* v_s_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_329_, v___y_330_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(lean_object* v_s_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1));
v___x_349_ = l_Lean_MessageData_ofFormat(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(lean_object* v_x_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(lean_object* v_c_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_lhs_358_; lean_object* v_rhs_359_; lean_object* v___x_360_; lean_object* v_a_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_394_; 
v_lhs_358_ = lean_ctor_get(v_c_355_, 0);
lean_inc_ref(v_lhs_358_);
v_rhs_359_ = lean_ctor_get(v_c_355_, 1);
lean_inc_ref(v_rhs_359_);
lean_dec_ref(v_c_355_);
lean_inc_ref(v___y_356_);
v___x_360_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_358_, v___y_356_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref(v___x_360_);
v_fst_362_ = lean_ctor_get(v_a_361_, 0);
v_snd_363_ = lean_ctor_get(v_a_361_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_394_ == 0)
{
v___x_365_ = v_a_361_;
v_isShared_366_ = v_isSharedCheck_394_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_362_);
lean_dec(v_a_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_394_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_393_; 
v___x_367_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_359_, v_snd_363_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_393_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_393_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_393_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v_fst_372_; lean_object* v_snd_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_392_; 
v_fst_372_ = lean_ctor_get(v_a_368_, 0);
v_snd_373_ = lean_ctor_get(v_a_368_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_368_);
if (v_isSharedCheck_392_ == 0)
{
v___x_375_ = v_a_368_;
v_isShared_376_ = v_isSharedCheck_392_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_snd_373_);
lean_inc(v_fst_372_);
lean_dec(v_a_368_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_392_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_type_377_; lean_object* v_u_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v_type_377_ = lean_ctor_get(v___y_356_, 1);
lean_inc_ref(v_type_377_);
v_u_378_ = lean_ctor_get(v___y_356_, 2);
lean_inc(v_u_378_);
lean_dec_ref(v___y_356_);
v___x_379_ = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1));
v___x_380_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
lean_ctor_set(v___x_365_, 1, v___x_380_);
lean_ctor_set(v___x_365_, 0, v_u_378_);
v___x_382_ = v___x_365_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_u_378_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_391_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = l_Lean_mkConst(v___x_379_, v___x_382_);
v___x_384_ = l_Lean_mkApp3(v___x_383_, v_type_377_, v_fst_362_, v_fst_372_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_384_);
v___x_386_ = v___x_375_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_snd_373_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_386_);
v___x_388_ = v___x_370_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___boxed(lean_object* v_c_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_395_, v___y_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(lean_object* v_as_399_, size_t v_sz_400_, size_t v_i_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_b_402_);
lean_ctor_set(v___x_410_, 1, v___y_403_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_snd_412_; lean_object* v_a_413_; lean_object* v___x_414_; 
v_snd_412_ = lean_ctor_get(v_b_402_, 1);
lean_inc(v_snd_412_);
lean_dec_ref(v_b_402_);
v_a_413_ = lean_array_uget_borrowed(v_as_399_, v_i_401_);
lean_inc(v_a_413_);
v___x_414_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_413_, v___y_403_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_431_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
v_fst_416_ = lean_ctor_get(v_a_415_, 0);
v_snd_417_ = lean_ctor_get(v_a_415_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_431_ == 0)
{
v___x_419_ = v_a_415_;
v_isShared_420_ = v_isSharedCheck_431_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
lean_dec(v_a_415_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_431_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_421_ = lean_box(0);
v___x_422_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_423_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_416_, v___x_422_);
v___x_424_ = lean_array_push(v_snd_412_, v___x_423_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_424_);
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
size_t v___x_427_; size_t v___x_428_; 
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_401_, v___x_427_);
v_i_401_ = v___x_428_;
v_b_402_ = v___x_426_;
v___y_403_ = v_snd_417_;
goto _start;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_snd_412_);
v_a_432_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_414_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_414_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_as_440_, lean_object* v_sz_441_, lean_object* v_i_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
size_t v_sz_boxed_450_; size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_sz_boxed_450_ = lean_unbox_usize(v_sz_441_);
lean_dec(v_sz_441_);
v_i_boxed_451_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_440_, v_sz_boxed_450_, v_i_boxed_451_, v_b_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v_as_440_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(lean_object* v_as_453_, size_t v_sz_454_, size_t v_i_455_, lean_object* v_b_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_455_, v_sz_454_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_b_456_);
lean_ctor_set(v___x_464_, 1, v___y_457_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
else
{
lean_object* v_snd_466_; lean_object* v_a_467_; lean_object* v___x_468_; 
v_snd_466_ = lean_ctor_get(v_b_456_, 1);
lean_inc(v_snd_466_);
lean_dec_ref(v_b_456_);
v_a_467_ = lean_array_uget_borrowed(v_as_453_, v_i_455_);
lean_inc(v_a_467_);
v___x_468_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_467_, v___y_457_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_485_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v_fst_470_ = lean_ctor_get(v_a_469_, 0);
v_snd_471_ = lean_ctor_get(v_a_469_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_485_ == 0)
{
v___x_473_ = v_a_469_;
v_isShared_474_ = v_isSharedCheck_485_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v_a_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_485_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_475_ = lean_box(0);
v___x_476_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_477_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_470_, v___x_476_);
v___x_478_ = lean_array_push(v_snd_466_, v___x_477_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_478_);
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_i_455_, v___x_481_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_453_, v_sz_454_, v___x_482_, v___x_480_, v_snd_471_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
return v___x_483_;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_snd_466_);
v_a_486_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_468_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_468_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2___boxed(lean_object* v_as_494_, lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_505_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_494_, v_sz_boxed_504_, v_i_boxed_505_, v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_as_494_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_507_, size_t v_sz_508_, size_t v_i_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_lt(v_i_509_, v_sz_508_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_b_510_);
lean_ctor_set(v___x_518_, 1, v___y_511_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v_snd_520_; lean_object* v_a_521_; lean_object* v___x_522_; 
v_snd_520_ = lean_ctor_get(v_b_510_, 1);
lean_inc(v_snd_520_);
lean_dec_ref(v_b_510_);
v_a_521_ = lean_array_uget_borrowed(v_as_507_, v_i_509_);
lean_inc(v_a_521_);
v___x_522_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_521_, v___y_511_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_539_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v_fst_524_ = lean_ctor_get(v_a_523_, 0);
v_snd_525_ = lean_ctor_get(v_a_523_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_539_ == 0)
{
v___x_527_ = v_a_523_;
v_isShared_528_ = v_isSharedCheck_539_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snd_525_);
lean_inc(v_fst_524_);
lean_dec(v_a_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_539_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_529_ = lean_box(0);
v___x_530_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_531_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_524_, v___x_530_);
v___x_532_ = lean_array_push(v_snd_520_, v___x_531_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_532_);
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
size_t v___x_535_; size_t v___x_536_; 
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_509_, v___x_535_);
v_i_509_ = v___x_536_;
v_b_510_ = v___x_534_;
v___y_511_ = v_snd_525_;
goto _start;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_snd_520_);
v_a_540_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_522_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_522_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_548_, lean_object* v_sz_549_, lean_object* v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_549_);
lean_dec(v_sz_549_);
v_i_boxed_559_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_548_, v_sz_boxed_558_, v_i_boxed_559_, v_b_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec_ref(v_as_548_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(lean_object* v_as_561_, size_t v_sz_562_, size_t v_i_563_, lean_object* v_b_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_lt(v_i_563_, v_sz_562_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_b_564_);
lean_ctor_set(v___x_572_, 1, v___y_565_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_snd_574_; lean_object* v_a_575_; lean_object* v___x_576_; 
v_snd_574_ = lean_ctor_get(v_b_564_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v_b_564_);
v_a_575_ = lean_array_uget_borrowed(v_as_561_, v_i_563_);
lean_inc(v_a_575_);
v___x_576_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_575_, v___y_565_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_593_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_576_);
v_fst_578_ = lean_ctor_get(v_a_577_, 0);
v_snd_579_ = lean_ctor_get(v_a_577_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_a_577_);
if (v_isSharedCheck_593_ == 0)
{
v___x_581_ = v_a_577_;
v_isShared_582_ = v_isSharedCheck_593_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snd_579_);
lean_inc(v_fst_578_);
lean_dec(v_a_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_593_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_583_ = lean_box(0);
v___x_584_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_585_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_578_, v___x_584_);
v___x_586_ = lean_array_push(v_snd_574_, v___x_585_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_586_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_592_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_add(v_i_563_, v___x_589_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_561_, v_sz_562_, v___x_590_, v___x_588_, v_snd_579_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_591_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_snd_574_);
v_a_594_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_576_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_576_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_as_602_, lean_object* v_sz_603_, lean_object* v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v_i_boxed_613_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_602_, v_sz_boxed_612_, v_i_boxed_613_, v_b_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec_ref(v_as_602_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(lean_object* v_inh_615_, lean_object* v_n_616_, lean_object* v_b_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
if (lean_obj_tag(v_n_616_) == 0)
{
lean_object* v_cs_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_678_; 
v_cs_624_ = lean_ctor_get(v_n_616_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_n_616_);
if (v_isSharedCheck_678_ == 0)
{
v___x_626_ = v_n_616_;
v_isShared_627_ = v_isSharedCheck_678_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_cs_624_);
lean_dec(v_n_616_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_678_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; size_t v_sz_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_628_ = lean_box(0);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_b_617_);
v_sz_630_ = lean_array_size(v_cs_624_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_inh_615_, v_cs_624_, v_sz_630_, v___x_631_, v___x_629_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec_ref(v_cs_624_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_669_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_669_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_669_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_669_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_637_; lean_object* v_fst_638_; 
v_fst_637_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_fst_637_);
v_fst_638_ = lean_ctor_get(v_fst_637_, 0);
if (lean_obj_tag(v_fst_638_) == 0)
{
lean_object* v_snd_639_; lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_653_; 
v_snd_639_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_639_);
lean_dec(v_a_633_);
v_snd_640_ = lean_ctor_get(v_fst_637_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_fst_637_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_fst_637_, 0);
lean_dec(v_unused_654_);
v___x_642_ = v_fst_637_;
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_dec(v_fst_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
lean_ctor_set(v___x_626_, 0, v_snd_640_);
v___x_645_ = v___x_626_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_snd_640_);
v___x_645_ = v_reuseFailAlloc_652_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_snd_639_);
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_639_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_647_);
v___x_649_ = v___x_635_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_666_; 
lean_inc_ref(v_fst_638_);
lean_del_object(v___x_626_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_fst_637_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_667_ = lean_ctor_get(v_fst_637_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_fst_637_, 0);
lean_dec(v_unused_668_);
v___x_656_ = v_fst_637_;
v_isShared_657_ = v_isSharedCheck_666_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_fst_637_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_666_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_snd_658_; lean_object* v_val_659_; lean_object* v___x_661_; 
v_snd_658_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_658_);
lean_dec(v_a_633_);
v_val_659_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_val_659_);
lean_dec_ref(v_fst_638_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v_snd_658_);
lean_ctor_set(v___x_656_, 0, v_val_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_val_659_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_snd_658_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_661_);
v___x_663_ = v___x_635_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_del_object(v___x_626_);
v_a_670_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_632_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_632_);
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
else
{
lean_object* v_vs_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_733_; 
v_vs_679_ = lean_ctor_get(v_n_616_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_n_616_);
if (v_isSharedCheck_733_ == 0)
{
v___x_681_ = v_n_616_;
v_isShared_682_ = v_isSharedCheck_733_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_vs_679_);
lean_dec(v_n_616_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_733_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_b_617_);
v_sz_685_ = lean_array_size(v_vs_679_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_vs_679_, v_sz_685_, v___x_686_, v___x_684_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec_ref(v_vs_679_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_724_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_724_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_724_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_724_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fst_692_; lean_object* v_fst_693_; 
v_fst_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_fst_692_);
v_fst_693_ = lean_ctor_get(v_fst_692_, 0);
if (lean_obj_tag(v_fst_693_) == 0)
{
lean_object* v_snd_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_708_; 
v_snd_694_ = lean_ctor_get(v_a_688_, 1);
lean_inc(v_snd_694_);
lean_dec(v_a_688_);
v_snd_695_ = lean_ctor_get(v_fst_692_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_fst_692_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_fst_692_, 0);
lean_dec(v_unused_709_);
v___x_697_ = v_fst_692_;
v_isShared_698_ = v_isSharedCheck_708_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_dec(v_fst_692_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_708_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_snd_695_);
v___x_700_ = v___x_681_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_snd_695_);
v___x_700_ = v_reuseFailAlloc_707_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_snd_694_);
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_694_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_702_);
v___x_704_ = v___x_690_;
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
else
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_721_; 
lean_inc_ref(v_fst_693_);
lean_del_object(v___x_681_);
v_isSharedCheck_721_ = !lean_is_exclusive(v_fst_692_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; 
v_unused_722_ = lean_ctor_get(v_fst_692_, 1);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_fst_692_, 0);
lean_dec(v_unused_723_);
v___x_711_ = v_fst_692_;
v_isShared_712_ = v_isSharedCheck_721_;
goto v_resetjp_710_;
}
else
{
lean_dec(v_fst_692_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_721_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_snd_713_; lean_object* v_val_714_; lean_object* v___x_716_; 
v_snd_713_ = lean_ctor_get(v_a_688_, 1);
lean_inc(v_snd_713_);
lean_dec(v_a_688_);
v_val_714_ = lean_ctor_get(v_fst_693_, 0);
lean_inc(v_val_714_);
lean_dec_ref(v_fst_693_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v_snd_713_);
lean_ctor_set(v___x_711_, 0, v_val_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_val_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_713_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_716_);
v___x_718_ = v___x_690_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_681_);
v_a_725_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_687_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_687_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(lean_object* v_inh_734_, lean_object* v_as_735_, size_t v_sz_736_, size_t v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_lt(v_i_737_, v_sz_736_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_b_738_);
lean_ctor_set(v___x_746_, 1, v___y_739_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_798_; 
v_snd_748_ = lean_ctor_get(v_b_738_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_b_738_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_b_738_, 0);
lean_dec(v_unused_799_);
v___x_750_ = v_b_738_;
v_isShared_751_ = v_isSharedCheck_798_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_dec(v_b_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_798_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_array_uget_borrowed(v_as_735_, v_i_737_);
lean_inc(v_snd_748_);
lean_inc(v_a_752_);
v___x_753_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_inh_734_, v_a_752_, v_snd_748_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_789_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_789_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_789_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_789_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_fst_758_; 
v_fst_758_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_fst_758_);
if (lean_obj_tag(v_fst_758_) == 0)
{
lean_object* v_snd_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_773_; 
v_snd_759_ = lean_ctor_get(v_a_754_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_754_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_a_754_, 0);
lean_dec(v_unused_774_);
v___x_761_ = v_a_754_;
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snd_759_);
lean_dec(v_a_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v_fst_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_snd_748_);
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_snd_748_);
v___x_765_ = v_reuseFailAlloc_772_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v_snd_759_);
lean_ctor_set(v___x_750_, 0, v___x_765_);
v___x_767_ = v___x_750_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_759_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_767_);
v___x_769_ = v___x_756_;
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
}
}
}
else
{
lean_object* v_snd_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
lean_del_object(v___x_756_);
lean_del_object(v___x_750_);
lean_dec(v_snd_748_);
v_snd_775_ = lean_ctor_get(v_a_754_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_754_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_a_754_, 0);
lean_dec(v_unused_788_);
v___x_777_ = v_a_754_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snd_775_);
lean_dec(v_a_754_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v_a_779_ = lean_ctor_get(v_fst_758_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v_fst_758_);
v___x_780_ = lean_box(0);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_a_779_);
lean_ctor_set(v___x_777_, 0, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_a_779_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
size_t v___x_783_; size_t v___x_784_; 
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_737_, v___x_783_);
v_i_737_ = v___x_784_;
v_b_738_ = v___x_782_;
v___y_739_ = v_snd_775_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_del_object(v___x_750_);
lean_dec(v_snd_748_);
v_a_790_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_753_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_753_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_inh_800_, lean_object* v_as_801_, lean_object* v_sz_802_, lean_object* v_i_803_, lean_object* v_b_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
size_t v_sz_boxed_811_; size_t v_i_boxed_812_; lean_object* v_res_813_; 
v_sz_boxed_811_ = lean_unbox_usize(v_sz_802_);
lean_dec(v_sz_802_);
v_i_boxed_812_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_inh_800_, v_as_801_, v_sz_boxed_811_, v_i_boxed_812_, v_b_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec_ref(v_as_801_);
lean_dec_ref(v_inh_800_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(lean_object* v_inh_814_, lean_object* v_n_815_, lean_object* v_b_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_inh_814_, v_n_815_, v_b_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v_inh_814_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(lean_object* v_t_824_, lean_object* v_init_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_b_833_; lean_object* v___y_834_; lean_object* v_root_837_; lean_object* v_tail_838_; lean_object* v___x_839_; 
v_root_837_ = lean_ctor_get(v_t_824_, 0);
lean_inc_ref(v_root_837_);
v_tail_838_ = lean_ctor_get(v_t_824_, 1);
lean_inc_ref(v_tail_838_);
lean_dec_ref(v_t_824_);
lean_inc_ref(v_init_825_);
v___x_839_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_825_, v_root_837_, v_init_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec_ref(v_init_825_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_fst_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
v_fst_841_ = lean_ctor_get(v_a_840_, 0);
lean_inc(v_fst_841_);
if (lean_obj_tag(v_fst_841_) == 0)
{
lean_object* v_snd_842_; lean_object* v_a_843_; 
lean_dec_ref(v_tail_838_);
v_snd_842_ = lean_ctor_get(v_a_840_, 1);
lean_inc(v_snd_842_);
lean_dec(v_a_840_);
v_a_843_ = lean_ctor_get(v_fst_841_, 0);
lean_inc(v_a_843_);
lean_dec_ref(v_fst_841_);
v_b_833_ = v_a_843_;
v___y_834_ = v_snd_842_;
goto v___jp_832_;
}
else
{
lean_object* v_snd_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_886_; 
v_snd_844_ = lean_ctor_get(v_a_840_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_a_840_, 0);
lean_dec(v_unused_887_);
v___x_846_ = v_a_840_;
v_isShared_847_ = v_isSharedCheck_886_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_snd_844_);
lean_dec(v_a_840_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_886_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v_a_848_ = lean_ctor_get(v_fst_841_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v_fst_841_);
v___x_849_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_a_848_);
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_848_);
v___x_851_ = v_reuseFailAlloc_885_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_sz_852_ = lean_array_size(v_tail_838_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_tail_838_, v_sz_852_, v___x_853_, v___x_851_, v_snd_844_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec_ref(v_tail_838_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_876_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_876_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_876_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_876_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_fst_859_; lean_object* v_fst_860_; 
v_fst_859_ = lean_ctor_get(v_a_855_, 0);
lean_inc(v_fst_859_);
v_fst_860_ = lean_ctor_get(v_fst_859_, 0);
if (lean_obj_tag(v_fst_860_) == 0)
{
lean_object* v_snd_861_; lean_object* v_snd_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_872_; 
v_snd_861_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_snd_861_);
lean_dec(v_a_855_);
v_snd_862_ = lean_ctor_get(v_fst_859_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_fst_859_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_fst_859_, 0);
lean_dec(v_unused_873_);
v___x_864_ = v_fst_859_;
v_isShared_865_ = v_isSharedCheck_872_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snd_862_);
lean_dec(v_fst_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_872_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_snd_861_);
lean_ctor_set(v___x_864_, 0, v_snd_862_);
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_snd_862_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_861_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_867_);
v___x_869_ = v___x_857_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_snd_874_; lean_object* v_val_875_; 
lean_inc_ref(v_fst_860_);
lean_dec(v_fst_859_);
lean_del_object(v___x_857_);
v_snd_874_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_snd_874_);
lean_dec(v_a_855_);
v_val_875_ = lean_ctor_get(v_fst_860_, 0);
lean_inc(v_val_875_);
lean_dec_ref(v_fst_860_);
v_b_833_ = v_val_875_;
v___y_834_ = v_snd_874_;
goto v___jp_832_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_854_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_854_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_tail_838_);
v_a_888_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_839_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_839_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
v___jp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_b_833_);
lean_ctor_set(v___x_835_, 1, v___y_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1___boxed(lean_object* v_t_896_, lean_object* v_init_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_896_, v_init_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3(void){
_start:
{
lean_object* v___f_909_; lean_object* v___x_910_; 
v___f_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0));
v___x_910_ = lean_mk_thunk(v___f_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_diseqs_917_; lean_object* v_diseqs_918_; lean_object* v___x_919_; 
v_diseqs_917_ = lean_ctor_get(v_a_911_, 16);
lean_inc_ref(v_diseqs_917_);
v_diseqs_918_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_919_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_diseqs_917_, v_diseqs_918_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_939_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_939_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_939_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_939_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_938_; 
v_fst_924_ = lean_ctor_get(v_a_920_, 0);
v_snd_925_ = lean_ctor_get(v_a_920_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_a_920_);
if (v_isSharedCheck_938_ == 0)
{
v___x_927_ = v_a_920_;
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v_a_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2));
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3);
v___x_931_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_929_, v___x_930_, v_fst_924_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_931_);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_snd_925_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_933_);
v___x_935_ = v___x_922_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_940_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_919_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_919_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___boxed(lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(lean_object* v_c_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_955_, v___y_956_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(lean_object* v_c_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(lean_object* v_e_971_, lean_object* v_cls_972_){
_start:
{
lean_object* v___x_973_; double v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_975_ = 1;
v___x_976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_977_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_977_, 0, v_cls_972_);
lean_ctor_set(v___x_977_, 1, v___x_973_);
lean_ctor_set(v___x_977_, 2, v___x_976_);
lean_ctor_set_float(v___x_977_, sizeof(void*)*3, v___x_974_);
lean_ctor_set_float(v___x_977_, sizeof(void*)*3 + 8, v___x_974_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*3 + 16, v___x_975_);
v___x_978_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_979_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v_e_971_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(lean_object* v_e_980_, lean_object* v_cls_981_){
_start:
{
lean_object* v___x_982_; double v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_982_ = lean_box(0);
v___x_983_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_984_ = 1;
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_986_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_986_, 0, v_cls_981_);
lean_ctor_set(v___x_986_, 1, v___x_982_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
lean_ctor_set_float(v___x_986_, sizeof(void*)*3, v___x_983_);
lean_ctor_set_float(v___x_986_, sizeof(void*)*3 + 8, v___x_983_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3 + 16, v___x_984_);
v___x_987_ = l_Lean_stringToMessageData(v_e_980_);
v___x_988_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_989_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_989_, 0, v___x_986_);
lean_ctor_set(v___x_989_, 1, v___x_987_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(lean_object* v___y_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_op_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_op_998_ = lean_ctor_get(v___y_996_, 3);
lean_inc_ref(v_op_998_);
lean_dec_ref(v___y_996_);
v___x_999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1);
v___x_1000_ = l_Lean_MessageData_ofExpr(v_op_998_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1));
v___x_1008_ = l_Lean_MessageData_ofFormat(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2);
return v___x_1010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5(void){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; 
v___f_1018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2));
v___x_1019_ = lean_mk_thunk(v___f_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8));
v___x_1026_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10));
v___x_1030_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12(void){
_start:
{
lean_object* v___x_1031_; lean_object* v_msgs_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11);
v_msgs_1032_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1033_ = lean_array_push(v_msgs_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_msgs_1041_; lean_object* v___y_1042_; lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1110_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref(v___x_1049_);
v_fst_1051_ = lean_ctor_get(v_a_1050_, 0);
v_snd_1052_ = lean_ctor_get(v_a_1050_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_a_1050_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1054_ = v_a_1050_;
v_isShared_1055_ = v_isSharedCheck_1110_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v_a_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1110_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_snd_1052_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1109_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v_fst_1058_ = lean_ctor_get(v_a_1057_, 0);
v_snd_1059_ = lean_ctor_get(v_a_1057_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_a_1057_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1061_ = v_a_1057_;
v_isShared_1062_ = v_isSharedCheck_1109_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snd_1059_);
lean_inc(v_fst_1058_);
lean_dec(v_a_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1109_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v_msgs_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v_msgs_1064_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1065_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v_msgs_1064_, v_fst_1051_);
v___x_1066_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v___x_1065_, v_fst_1058_);
v___x_1067_ = lean_array_get_size(v___x_1066_);
v___x_1068_ = lean_nat_dec_eq(v___x_1067_, v___x_1063_);
if (v___x_1068_ == 0)
{
lean_object* v_neutral_x3f_1069_; lean_object* v_idempotentInst_x3f_1070_; lean_object* v_commInst_x3f_1071_; lean_object* v_info_1073_; lean_object* v___y_1074_; lean_object* v_info_1080_; lean_object* v___y_1081_; lean_object* v_neutral_x3f_1082_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v_info_1103_; lean_object* v___y_1104_; lean_object* v_neutral_x3f_1105_; lean_object* v_idempotentInst_x3f_1106_; 
v_neutral_x3f_1069_ = lean_ctor_get(v_snd_1059_, 4);
lean_inc(v_neutral_x3f_1069_);
v_idempotentInst_x3f_1070_ = lean_ctor_get(v_snd_1059_, 6);
lean_inc(v_idempotentInst_x3f_1070_);
v_commInst_x3f_1071_ = lean_ctor_get(v_snd_1059_, 7);
if (lean_obj_tag(v_commInst_x3f_1071_) == 0)
{
if (v___x_1068_ == 0)
{
v_info_1103_ = v_msgs_1064_;
v___y_1104_ = v_snd_1059_;
v_neutral_x3f_1105_ = v_neutral_x3f_1069_;
v_idempotentInst_x3f_1106_ = v_idempotentInst_x3f_1070_;
goto v___jp_1102_;
}
else
{
goto v___jp_1107_;
}
}
else
{
goto v___jp_1107_;
}
v___jp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4));
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5);
v___x_1077_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_1075_, v___x_1076_, v_info_1073_);
v___x_1078_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v___x_1066_, v___x_1077_);
v_msgs_1041_ = v___x_1078_;
v___y_1042_ = v___y_1074_;
goto v___jp_1040_;
}
v___jp_1079_:
{
if (lean_obj_tag(v_neutral_x3f_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v_val_1083_ = lean_ctor_get(v_neutral_x3f_1082_, 0);
lean_inc(v_val_1083_);
lean_dec_ref(v_neutral_x3f_1082_);
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7);
v___x_1085_ = l_Lean_MessageData_ofExpr(v_val_1083_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 7);
lean_ctor_set(v___x_1061_, 1, v___x_1085_);
lean_ctor_set(v___x_1061_, 0, v___x_1084_);
v___x_1087_ = v___x_1061_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 7);
lean_ctor_set(v___x_1054_, 1, v___x_1088_);
lean_ctor_set(v___x_1054_, 0, v___x_1087_);
v___x_1090_ = v___x_1054_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1092_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(v___x_1090_, v___x_1091_);
v___x_1093_ = lean_array_push(v_info_1080_, v___x_1092_);
v_info_1073_ = v___x_1093_;
v___y_1074_ = v___y_1081_;
goto v___jp_1072_;
}
}
}
else
{
lean_dec(v_neutral_x3f_1082_);
lean_del_object(v___x_1061_);
lean_del_object(v___x_1054_);
v_info_1073_ = v_info_1080_;
v___y_1074_ = v___y_1081_;
goto v___jp_1072_;
}
}
v___jp_1096_:
{
lean_object* v_neutral_x3f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_neutral_x3f_1099_ = lean_ctor_get(v___y_1097_, 4);
lean_inc(v_neutral_x3f_1099_);
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9);
v___x_1101_ = lean_array_push(v___y_1098_, v___x_1100_);
v_info_1080_ = v___x_1101_;
v___y_1081_ = v___y_1097_;
v_neutral_x3f_1082_ = v_neutral_x3f_1099_;
goto v___jp_1079_;
}
v___jp_1102_:
{
if (lean_obj_tag(v_idempotentInst_x3f_1106_) == 0)
{
if (v___x_1068_ == 0)
{
v_info_1080_ = v_info_1103_;
v___y_1081_ = v___y_1104_;
v_neutral_x3f_1082_ = v_neutral_x3f_1105_;
goto v___jp_1079_;
}
else
{
lean_dec(v_neutral_x3f_1105_);
v___y_1097_ = v___y_1104_;
v___y_1098_ = v_info_1103_;
goto v___jp_1096_;
}
}
else
{
lean_dec_ref(v_idempotentInst_x3f_1106_);
lean_dec(v_neutral_x3f_1105_);
v___y_1097_ = v___y_1104_;
v___y_1098_ = v_info_1103_;
goto v___jp_1096_;
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12);
v_info_1103_ = v___x_1108_;
v___y_1104_ = v_snd_1059_;
v_neutral_x3f_1105_ = v_neutral_x3f_1069_;
v_idempotentInst_x3f_1106_ = v_idempotentInst_x3f_1070_;
goto v___jp_1102_;
}
}
else
{
lean_del_object(v___x_1061_);
lean_del_object(v___x_1054_);
v_msgs_1041_ = v___x_1066_;
v___y_1042_ = v_snd_1059_;
goto v___jp_1040_;
}
}
}
else
{
lean_del_object(v___x_1054_);
lean_dec(v_fst_1051_);
return v___x_1056_;
}
}
}
else
{
return v___x_1049_;
}
v___jp_1040_:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc_ref(v___y_1042_);
v___f_1043_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1043_, 0, v___y_1042_);
v___x_1044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1));
v___x_1045_ = lean_mk_thunk(v___f_1043_);
v___x_1046_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_1044_, v___x_1045_, v_msgs_1041_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___y_1042_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___boxed(lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(lean_object* v_as_1118_, size_t v_sz_1119_, size_t v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_a_1128_; uint8_t v___x_1132_; 
v___x_1132_ = lean_usize_dec_lt(v_i_1120_, v_sz_1119_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_b_1121_);
return v___x_1133_;
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_array_uget_borrowed(v_as_1118_, v_i_1120_);
lean_inc(v_a_1134_);
v___x_1135_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1134_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v_fst_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
v_fst_1137_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_fst_1137_);
lean_dec(v_a_1136_);
if (lean_obj_tag(v_fst_1137_) == 1)
{
lean_object* v_val_1138_; lean_object* v___x_1139_; 
v_val_1138_ = lean_ctor_get(v_fst_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v_fst_1137_);
v___x_1139_ = lean_array_push(v_b_1121_, v_val_1138_);
v_a_1128_ = v___x_1139_;
goto v___jp_1127_;
}
else
{
lean_dec(v_fst_1137_);
v_a_1128_ = v_b_1121_;
goto v___jp_1127_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_b_1121_);
v_a_1140_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1135_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1135_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
v___jp_1127_:
{
size_t v___x_1129_; size_t v___x_1130_; 
v___x_1129_ = ((size_t)1ULL);
v___x_1130_ = lean_usize_add(v_i_1120_, v___x_1129_);
v_i_1120_ = v___x_1130_;
v_b_1121_ = v_a_1128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0___boxed(lean_object* v_as_1148_, lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_1148_, v_sz_boxed_1157_, v_i_boxed_1158_, v_b_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v_as_1148_);
return v_res_1159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0(void){
_start:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; double v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_1161_ = 1;
v___x_1162_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_1163_ = lean_box(0);
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1));
v___x_1165_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v___x_1160_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3, v___x_1162_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3 + 8, v___x_1162_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*3 + 16, v___x_1161_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Meta_Grind_AC_pp_x3f___closed__2));
v___x_1170_ = l_Lean_MessageData_ofFormat(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f(lean_object* v_goal_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1178_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1177_, v_goal_1171_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v_structs_1180_; lean_object* v___x_1181_; lean_object* v_msgs_1182_; size_t v_sz_1183_; size_t v___x_1184_; lean_object* v___x_1185_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1178_);
v_structs_1180_ = lean_ctor_get(v_a_1179_, 0);
lean_inc_ref(v_structs_1180_);
lean_dec(v_a_1179_);
v___x_1181_ = lean_unsigned_to_nat(0u);
v_msgs_1182_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v_sz_1183_ = lean_array_size(v_structs_1180_);
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_structs_1180_, v_sz_1183_, v___x_1184_, v_msgs_1182_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec_ref(v_structs_1180_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1210_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1210_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1210_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_array_get_size(v_a_1186_);
v___x_1191_ = lean_nat_dec_eq(v___x_1190_, v___x_1181_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_dec_eq(v___x_1190_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Grind_AC_pp_x3f___closed__0, &l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once, _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0);
v___x_1195_ = lean_obj_once(&l_Lean_Meta_Grind_AC_pp_x3f___closed__3, &l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once, _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3);
v___x_1196_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
lean_ctor_set(v___x_1196_, 2, v_a_1186_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1197_);
v___x_1199_ = v___x_1188_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = lean_array_fget(v_a_1186_, v___x_1181_);
lean_dec(v_a_1186_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1202_);
v___x_1204_ = v___x_1188_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_dec(v_a_1186_);
v___x_1206_ = lean_box(0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1206_);
v___x_1208_ = v___x_1188_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
v_a_1211_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1185_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1185_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1231_; 
v_a_1219_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1221_ = v___x_1178_;
v_isShared_1222_ = v_isSharedCheck_1231_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1178_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1231_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_ref_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v_ref_1223_ = lean_ctor_get(v_a_1174_, 5);
v___x_1224_ = lean_io_error_to_string(v_a_1219_);
v___x_1225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
v___x_1226_ = l_Lean_MessageData_ofFormat(v___x_1225_);
lean_inc(v_ref_1223_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_ref_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1227_);
v___x_1229_ = v___x_1221_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f___boxed(lean_object* v_goal_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Meta_Grind_AC_pp_x3f(v_goal_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec_ref(v_goal_1232_);
return v_res_1238_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM = _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
}
#ifdef __cplusplus
}
#endif
