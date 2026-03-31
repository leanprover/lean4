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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM(void){
_start:
{
lean_object* v___x_8_; lean_object* v_toApplicative_9_; lean_object* v_toFunctor_10_; lean_object* v_toSeq_11_; lean_object* v_toSeqLeft_12_; lean_object* v_toSeqRight_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toApplicative_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_53_; 
v___x_8_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1);
v_toApplicative_9_ = lean_ctor_get(v___x_8_, 0);
v_toFunctor_10_ = lean_ctor_get(v_toApplicative_9_, 0);
v_toSeq_11_ = lean_ctor_get(v_toApplicative_9_, 2);
v_toSeqLeft_12_ = lean_ctor_get(v_toApplicative_9_, 3);
v_toSeqRight_13_ = lean_ctor_get(v_toApplicative_9_, 4);
v___f_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2));
v___f_15_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3));
lean_inc_ref_n(v_toFunctor_10_, 2);
v___f_16_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_16_, 0, v_toFunctor_10_);
v___f_17_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_17_, 0, v_toFunctor_10_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___f_16_);
lean_ctor_set(v___x_18_, 1, v___f_17_);
lean_inc(v_toSeqRight_13_);
v___f_19_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_19_, 0, v_toSeqRight_13_);
lean_inc(v_toSeqLeft_12_);
v___f_20_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_20_, 0, v_toSeqLeft_12_);
lean_inc(v_toSeq_11_);
v___f_21_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_21_, 0, v_toSeq_11_);
v___x_22_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_22_, 0, v___x_18_);
lean_ctor_set(v___x_22_, 1, v___f_14_);
lean_ctor_set(v___x_22_, 2, v___f_21_);
lean_ctor_set(v___x_22_, 3, v___f_20_);
lean_ctor_set(v___x_22_, 4, v___f_19_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v___f_15_);
v___x_24_ = l_StateRefT_x27_instMonad___redArg(v___x_23_);
v_toApplicative_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v___x_24_, 1);
lean_dec(v_unused_54_);
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_53_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_toApplicative_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_53_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_toFunctor_29_; lean_object* v_toSeq_30_; lean_object* v_toSeqLeft_31_; lean_object* v_toSeqRight_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_51_; 
v_toFunctor_29_ = lean_ctor_get(v_toApplicative_25_, 0);
v_toSeq_30_ = lean_ctor_get(v_toApplicative_25_, 2);
v_toSeqLeft_31_ = lean_ctor_get(v_toApplicative_25_, 3);
v_toSeqRight_32_ = lean_ctor_get(v_toApplicative_25_, 4);
v_isSharedCheck_51_ = !lean_is_exclusive(v_toApplicative_25_);
if (v_isSharedCheck_51_ == 0)
{
lean_object* v_unused_52_; 
v_unused_52_ = lean_ctor_get(v_toApplicative_25_, 1);
lean_dec(v_unused_52_);
v___x_34_ = v_toApplicative_25_;
v_isShared_35_ = v_isSharedCheck_51_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_toSeqRight_32_);
lean_inc(v_toSeqLeft_31_);
lean_inc(v_toSeq_30_);
lean_inc(v_toFunctor_29_);
lean_dec(v_toApplicative_25_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_51_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___x_45_; 
v___f_36_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4));
v___f_37_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5));
lean_inc_ref(v_toFunctor_29_);
v___f_38_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_38_, 0, v_toFunctor_29_);
v___f_39_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_39_, 0, v_toFunctor_29_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v___f_38_);
lean_ctor_set(v___x_40_, 1, v___f_39_);
v___f_41_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_41_, 0, v_toSeqRight_32_);
v___f_42_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_42_, 0, v_toSeqLeft_31_);
v___f_43_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_43_, 0, v_toSeq_30_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v___f_41_);
lean_ctor_set(v___x_34_, 3, v___f_42_);
lean_ctor_set(v___x_34_, 2, v___f_43_);
lean_ctor_set(v___x_34_, 1, v___f_36_);
lean_ctor_set(v___x_34_, 0, v___x_40_);
v___x_45_ = v___x_34_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___f_36_);
lean_ctor_set(v_reuseFailAlloc_50_, 2, v___f_43_);
lean_ctor_set(v_reuseFailAlloc_50_, 3, v___f_42_);
lean_ctor_set(v_reuseFailAlloc_50_, 4, v___f_41_);
v___x_45_ = v_reuseFailAlloc_50_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_47_; 
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 1, v___f_37_);
lean_ctor_set(v___x_27_, 0, v___x_45_);
v___x_47_ = v___x_27_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___f_37_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; 
v___x_48_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_48_, 0, lean_box(0));
lean_closure_set(v___x_48_, 1, lean_box(0));
lean_closure_set(v___x_48_, 2, v___x_47_);
return v___x_48_;
}
}
}
}
}
}
static double _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0(void){
_start:
{
lean_object* v___x_55_; double v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_float_of_nat(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(lean_object* v_cls_58_, lean_object* v_header_59_, lean_object* v_msgs_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_array_get_size(v_msgs_60_);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_nat_dec_eq(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; lean_object* v___x_65_; double v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_64_ = 1;
v___x_65_ = lean_box(0);
v___x_66_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_68_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_68_, 0, v_cls_58_);
lean_ctor_set(v___x_68_, 1, v___x_65_);
lean_ctor_set(v___x_68_, 2, v___x_67_);
lean_ctor_set_float(v___x_68_, sizeof(void*)*3, v___x_66_);
lean_ctor_set_float(v___x_68_, sizeof(void*)*3 + 8, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*3 + 16, v___x_64_);
v___x_69_ = lean_thunk_get_own(v_header_59_);
v___x_70_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
lean_ctor_set(v___x_70_, 2, v_msgs_60_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; 
lean_dec_ref(v_msgs_60_);
lean_dec(v_cls_58_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___boxed(lean_object* v_cls_73_, lean_object* v_header_74_, lean_object* v_msgs_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v_cls_73_, v_header_74_, v_msgs_75_);
lean_dec_ref(v_header_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(lean_object* v_msgs_77_, lean_object* v_msg_x3f_78_){
_start:
{
if (lean_obj_tag(v_msg_x3f_78_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_80_; 
v_val_79_ = lean_ctor_get(v_msg_x3f_78_, 0);
lean_inc(v_val_79_);
lean_dec_ref(v_msg_x3f_78_);
v___x_80_ = lean_array_push(v_msgs_77_, v_val_79_);
return v___x_80_;
}
else
{
lean_dec(v_msg_x3f_78_);
return v_msgs_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(lean_object* v_e_83_, lean_object* v_cls_84_){
_start:
{
lean_object* v___x_85_; double v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_85_ = lean_box(0);
v___x_86_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_87_ = 1;
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_89_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_89_, 0, v_cls_84_);
lean_ctor_set(v___x_89_, 1, v___x_85_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
lean_ctor_set_float(v___x_89_, sizeof(void*)*3, v___x_86_);
lean_ctor_set_float(v___x_89_, sizeof(void*)*3 + 8, v___x_86_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*3 + 16, v___x_87_);
v___x_90_ = l_Lean_MessageData_ofExpr(v_e_83_);
v___x_91_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_92_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_92_, 0, v___x_89_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1));
v___x_97_ = l_Lean_MessageData_ofFormat(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0(lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(lean_object* v_s_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_s_100_) == 0)
{
lean_object* v_vars_104_; lean_object* v_x_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_121_; 
v_vars_104_ = lean_ctor_get(v___y_101_, 10);
v_x_105_ = lean_ctor_get(v_s_100_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v_s_100_);
if (v_isSharedCheck_121_ == 0)
{
v___x_107_ = v_s_100_;
v_isShared_108_ = v_isSharedCheck_121_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_x_105_);
lean_dec(v_s_100_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_121_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_size_109_; uint8_t v___x_110_; 
v_size_109_ = lean_ctor_get(v_vars_104_, 2);
v___x_110_ = lean_nat_dec_lt(v_x_105_, v_size_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
lean_dec(v_x_105_);
v___x_111_ = l_outOfBounds___redArg(v___x_103_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___y_101_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_112_);
v___x_114_ = v___x_107_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = l_Lean_PersistentArray_get_x21___redArg(v___x_103_, v_vars_104_, v_x_105_);
lean_dec(v_x_105_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___y_101_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_117_);
v___x_119_ = v___x_107_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
else
{
lean_object* v_x_122_; lean_object* v_s_123_; lean_object* v___x_124_; lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_150_; 
v_x_122_ = lean_ctor_get(v_s_100_, 0);
lean_inc(v_x_122_);
v_s_123_ = lean_ctor_get(v_s_100_, 1);
lean_inc_ref(v_s_123_);
lean_dec_ref(v_s_100_);
lean_inc_ref(v___y_101_);
v___x_124_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_123_, v___y_101_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_150_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_150_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_150_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_fst_129_; lean_object* v_snd_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_149_; 
v_fst_129_ = lean_ctor_get(v_a_125_, 0);
v_snd_130_ = lean_ctor_get(v_a_125_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_125_);
if (v_isSharedCheck_149_ == 0)
{
v___x_132_ = v_a_125_;
v_isShared_133_ = v_isSharedCheck_149_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_snd_130_);
lean_inc(v_fst_129_);
lean_dec(v_a_125_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_149_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_op_134_; lean_object* v_vars_135_; lean_object* v___y_137_; lean_object* v_size_145_; uint8_t v___x_146_; 
v_op_134_ = lean_ctor_get(v___y_101_, 3);
lean_inc_ref(v_op_134_);
v_vars_135_ = lean_ctor_get(v___y_101_, 10);
lean_inc_ref(v_vars_135_);
lean_dec_ref(v___y_101_);
v_size_145_ = lean_ctor_get(v_vars_135_, 2);
v___x_146_ = lean_nat_dec_lt(v_x_122_, v_size_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
lean_dec_ref(v_vars_135_);
lean_dec(v_x_122_);
v___x_147_ = l_outOfBounds___redArg(v___x_103_);
v___y_137_ = v___x_147_;
goto v___jp_136_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_PersistentArray_get_x21___redArg(v___x_103_, v_vars_135_, v_x_122_);
lean_dec(v_x_122_);
lean_dec_ref(v_vars_135_);
v___y_137_ = v___x_148_;
goto v___jp_136_;
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = l_Lean_mkAppB(v_op_134_, v___y_137_, v_fst_129_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_138_);
v___x_140_ = v___x_132_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_snd_130_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_140_);
v___x_142_ = v___x_127_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_s_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_151_, v___y_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(lean_object* v_c_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_lhs_165_; lean_object* v_rhs_166_; lean_object* v___x_167_; lean_object* v_a_168_; lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_201_; 
v_lhs_165_ = lean_ctor_get(v_c_158_, 0);
lean_inc_ref(v_lhs_165_);
v_rhs_166_ = lean_ctor_get(v_c_158_, 1);
lean_inc_ref(v_rhs_166_);
lean_dec_ref(v_c_158_);
lean_inc_ref(v___y_159_);
v___x_167_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_165_, v___y_159_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref(v___x_167_);
v_fst_169_ = lean_ctor_get(v_a_168_, 0);
v_snd_170_ = lean_ctor_get(v_a_168_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_a_168_);
if (v_isSharedCheck_201_ == 0)
{
v___x_172_ = v_a_168_;
v_isShared_173_ = v_isSharedCheck_201_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_snd_170_);
lean_inc(v_fst_169_);
lean_dec(v_a_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_201_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_200_; 
v___x_174_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_166_, v_snd_170_);
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_200_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_200_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_200_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_199_; 
v_fst_179_ = lean_ctor_get(v_a_175_, 0);
v_snd_180_ = lean_ctor_get(v_a_175_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_a_175_);
if (v_isSharedCheck_199_ == 0)
{
v___x_182_ = v_a_175_;
v_isShared_183_ = v_isSharedCheck_199_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_snd_180_);
lean_inc(v_fst_179_);
lean_dec(v_a_175_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_199_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_type_184_; lean_object* v_u_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v_type_184_ = lean_ctor_get(v___y_159_, 1);
lean_inc_ref(v_type_184_);
v_u_185_ = lean_ctor_get(v___y_159_, 2);
lean_inc(v_u_185_);
lean_dec_ref(v___y_159_);
v___x_186_ = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1));
v___x_187_ = lean_box(0);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 1);
lean_ctor_set(v___x_172_, 1, v___x_187_);
lean_ctor_set(v___x_172_, 0, v_u_185_);
v___x_189_ = v___x_172_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_u_185_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_187_);
v___x_189_ = v_reuseFailAlloc_198_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = l_Lean_mkConst(v___x_186_, v___x_189_);
v___x_191_ = l_Lean_mkApp3(v___x_190_, v_type_184_, v_fst_169_, v_fst_179_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_191_);
v___x_193_ = v___x_182_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_snd_180_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_193_);
v___x_195_ = v___x_177_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___boxed(lean_object* v_c_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(lean_object* v_as_x27_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
if (lean_obj_tag(v_as_x27_214_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_b_215_);
lean_ctor_set(v___x_222_, 1, v___y_216_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
else
{
lean_object* v_head_224_; lean_object* v_tail_225_; lean_object* v___x_226_; lean_object* v_a_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_head_224_ = lean_ctor_get(v_as_x27_214_, 0);
lean_inc(v_head_224_);
v_tail_225_ = lean_ctor_get(v_as_x27_214_, 1);
lean_inc(v_tail_225_);
lean_dec_ref(v_as_x27_214_);
v___x_226_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_head_224_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v_fst_228_ = lean_ctor_get(v_a_227_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_a_227_, 1);
lean_inc(v_snd_229_);
lean_dec(v_a_227_);
v___x_230_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_231_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_228_, v___x_230_);
v___x_232_ = lean_array_push(v_b_215_, v___x_231_);
v_as_x27_214_ = v_tail_225_;
v_b_215_ = v___x_232_;
v___y_216_ = v_snd_229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___boxed(lean_object* v_as_x27_234_, lean_object* v_b_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_234_, v_b_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3(void){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; 
v___f_247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0));
v___x_248_ = lean_mk_thunk(v___f_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_basis_255_; lean_object* v_basis_256_; lean_object* v___x_257_; 
v_basis_255_ = lean_ctor_get(v_a_249_, 15);
lean_inc(v_basis_255_);
v_basis_256_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_257_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_basis_255_, v_basis_256_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_277_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_277_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_277_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_277_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_276_; 
v_fst_262_ = lean_ctor_get(v_a_258_, 0);
v_snd_263_ = lean_ctor_get(v_a_258_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_a_258_);
if (v_isSharedCheck_276_ == 0)
{
v___x_265_ = v_a_258_;
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_snd_263_);
lean_inc(v_fst_262_);
lean_dec(v_a_258_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2));
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3);
v___x_269_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_267_, v___x_268_, v_fst_262_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_269_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_snd_263_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_271_);
v___x_273_ = v___x_260_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_257_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_257_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___boxed(lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(lean_object* v_as_293_, lean_object* v_as_x27_294_, lean_object* v_b_295_, lean_object* v_a_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_294_, v_b_295_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(lean_object* v_as_304_, lean_object* v_as_x27_305_, lean_object* v_b_306_, lean_object* v_a_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_304_, v_as_x27_305_, v_b_306_, v_a_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v_as_304_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(lean_object* v_s_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_315_, v___y_316_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(lean_object* v_s_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1));
v___x_335_ = l_Lean_MessageData_ofFormat(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(lean_object* v_c_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_lhs_344_; lean_object* v_rhs_345_; lean_object* v___x_346_; lean_object* v_a_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_380_; 
v_lhs_344_ = lean_ctor_get(v_c_341_, 0);
lean_inc_ref(v_lhs_344_);
v_rhs_345_ = lean_ctor_get(v_c_341_, 1);
lean_inc_ref(v_rhs_345_);
lean_dec_ref(v_c_341_);
lean_inc_ref(v___y_342_);
v___x_346_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_344_, v___y_342_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v_fst_348_ = lean_ctor_get(v_a_347_, 0);
v_snd_349_ = lean_ctor_get(v_a_347_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_a_347_);
if (v_isSharedCheck_380_ == 0)
{
v___x_351_ = v_a_347_;
v_isShared_352_ = v_isSharedCheck_380_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snd_349_);
lean_inc(v_fst_348_);
lean_dec(v_a_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_380_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_379_; 
v___x_353_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_345_, v_snd_349_);
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_379_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_379_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_379_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_378_; 
v_fst_358_ = lean_ctor_get(v_a_354_, 0);
v_snd_359_ = lean_ctor_get(v_a_354_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_a_354_);
if (v_isSharedCheck_378_ == 0)
{
v___x_361_ = v_a_354_;
v_isShared_362_ = v_isSharedCheck_378_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snd_359_);
lean_inc(v_fst_358_);
lean_dec(v_a_354_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_378_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_type_363_; lean_object* v_u_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v_type_363_ = lean_ctor_get(v___y_342_, 1);
lean_inc_ref(v_type_363_);
v_u_364_ = lean_ctor_get(v___y_342_, 2);
lean_inc(v_u_364_);
lean_dec_ref(v___y_342_);
v___x_365_ = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1));
v___x_366_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set_tag(v___x_351_, 1);
lean_ctor_set(v___x_351_, 1, v___x_366_);
lean_ctor_set(v___x_351_, 0, v_u_364_);
v___x_368_ = v___x_351_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_u_364_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_377_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_369_ = l_Lean_mkConst(v___x_365_, v___x_368_);
v___x_370_ = l_Lean_mkApp3(v___x_369_, v_type_363_, v_fst_348_, v_fst_358_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_370_);
v___x_372_ = v___x_361_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_snd_359_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_372_);
v___x_374_ = v___x_356_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___boxed(lean_object* v_c_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_381_, v___y_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(lean_object* v_as_385_, size_t v_sz_386_, size_t v_i_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_b_388_);
lean_ctor_set(v___x_396_, 1, v___y_389_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v_snd_398_; lean_object* v_a_399_; lean_object* v___x_400_; 
v_snd_398_ = lean_ctor_get(v_b_388_, 1);
lean_inc(v_snd_398_);
lean_dec_ref(v_b_388_);
v_a_399_ = lean_array_uget_borrowed(v_as_385_, v_i_387_);
lean_inc(v_a_399_);
v___x_400_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_399_, v___y_389_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_417_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v_fst_402_ = lean_ctor_get(v_a_401_, 0);
v_snd_403_ = lean_ctor_get(v_a_401_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_401_);
if (v_isSharedCheck_417_ == 0)
{
v___x_405_ = v_a_401_;
v_isShared_406_ = v_isSharedCheck_417_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snd_403_);
lean_inc(v_fst_402_);
lean_dec(v_a_401_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_417_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_407_ = lean_box(0);
v___x_408_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_409_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_402_, v___x_408_);
v___x_410_ = lean_array_push(v_snd_398_, v___x_409_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_410_);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_412_ = v___x_405_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_416_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
size_t v___x_413_; size_t v___x_414_; 
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_387_, v___x_413_);
v_i_387_ = v___x_414_;
v_b_388_ = v___x_412_;
v___y_389_ = v_snd_403_;
goto _start;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_snd_398_);
v_a_418_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_400_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_400_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_as_426_, lean_object* v_sz_427_, lean_object* v_i_428_, lean_object* v_b_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
size_t v_sz_boxed_436_; size_t v_i_boxed_437_; lean_object* v_res_438_; 
v_sz_boxed_436_ = lean_unbox_usize(v_sz_427_);
lean_dec(v_sz_427_);
v_i_boxed_437_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_426_, v_sz_boxed_436_, v_i_boxed_437_, v_b_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_as_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(lean_object* v_as_439_, size_t v_sz_440_, size_t v_i_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v_b_442_);
lean_ctor_set(v___x_450_, 1, v___y_443_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
else
{
lean_object* v_snd_452_; lean_object* v_a_453_; lean_object* v___x_454_; 
v_snd_452_ = lean_ctor_get(v_b_442_, 1);
lean_inc(v_snd_452_);
lean_dec_ref(v_b_442_);
v_a_453_ = lean_array_uget_borrowed(v_as_439_, v_i_441_);
lean_inc(v_a_453_);
v___x_454_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_453_, v___y_443_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_471_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref(v___x_454_);
v_fst_456_ = lean_ctor_get(v_a_455_, 0);
v_snd_457_ = lean_ctor_get(v_a_455_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_455_);
if (v_isSharedCheck_471_ == 0)
{
v___x_459_ = v_a_455_;
v_isShared_460_ = v_isSharedCheck_471_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_inc(v_fst_456_);
lean_dec(v_a_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_471_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_461_ = lean_box(0);
v___x_462_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_463_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_456_, v___x_462_);
v___x_464_ = lean_array_push(v_snd_452_, v___x_463_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_464_);
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_466_ = v___x_459_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_add(v_i_441_, v___x_467_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_439_, v_sz_440_, v___x_468_, v___x_466_, v_snd_457_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_469_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_snd_452_);
v_a_472_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_454_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_454_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2___boxed(lean_object* v_as_480_, lean_object* v_sz_481_, lean_object* v_i_482_, lean_object* v_b_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
size_t v_sz_boxed_490_; size_t v_i_boxed_491_; lean_object* v_res_492_; 
v_sz_boxed_490_ = lean_unbox_usize(v_sz_481_);
lean_dec(v_sz_481_);
v_i_boxed_491_ = lean_unbox_usize(v_i_482_);
lean_dec(v_i_482_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_480_, v_sz_boxed_490_, v_i_boxed_491_, v_b_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v_as_480_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_493_, size_t v_sz_494_, size_t v_i_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_lt(v_i_495_, v_sz_494_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_b_496_);
lean_ctor_set(v___x_504_, 1, v___y_497_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v_snd_506_; lean_object* v_a_507_; lean_object* v___x_508_; 
v_snd_506_ = lean_ctor_get(v_b_496_, 1);
lean_inc(v_snd_506_);
lean_dec_ref(v_b_496_);
v_a_507_ = lean_array_uget_borrowed(v_as_493_, v_i_495_);
lean_inc(v_a_507_);
v___x_508_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_507_, v___y_497_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_525_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v_fst_510_ = lean_ctor_get(v_a_509_, 0);
v_snd_511_ = lean_ctor_get(v_a_509_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_525_ == 0)
{
v___x_513_ = v_a_509_;
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_snd_511_);
lean_inc(v_fst_510_);
lean_dec(v_a_509_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_515_ = lean_box(0);
v___x_516_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_517_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_510_, v___x_516_);
v___x_518_ = lean_array_push(v_snd_506_, v___x_517_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_518_);
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_520_ = v___x_513_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
size_t v___x_521_; size_t v___x_522_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_495_, v___x_521_);
v_i_495_ = v___x_522_;
v_b_496_ = v___x_520_;
v___y_497_ = v_snd_511_;
goto _start;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_snd_506_);
v_a_526_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_508_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_508_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_534_, lean_object* v_sz_535_, lean_object* v_i_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_535_);
lean_dec(v_sz_535_);
v_i_boxed_545_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_534_, v_sz_boxed_544_, v_i_boxed_545_, v_b_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_as_534_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(lean_object* v_as_547_, size_t v_sz_548_, size_t v_i_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_549_, v_sz_548_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_b_550_);
lean_ctor_set(v___x_558_, 1, v___y_551_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v_snd_560_; lean_object* v_a_561_; lean_object* v___x_562_; 
v_snd_560_ = lean_ctor_get(v_b_550_, 1);
lean_inc(v_snd_560_);
lean_dec_ref(v_b_550_);
v_a_561_ = lean_array_uget_borrowed(v_as_547_, v_i_549_);
lean_inc(v_a_561_);
v___x_562_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_561_, v___y_551_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_579_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref(v___x_562_);
v_fst_564_ = lean_ctor_get(v_a_563_, 0);
v_snd_565_ = lean_ctor_get(v_a_563_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_563_);
if (v_isSharedCheck_579_ == 0)
{
v___x_567_ = v_a_563_;
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_inc(v_fst_564_);
lean_dec(v_a_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_569_ = lean_box(0);
v___x_570_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_571_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_564_, v___x_570_);
v___x_572_ = lean_array_push(v_snd_560_, v___x_571_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_572_);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_574_ = v___x_567_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_549_, v___x_575_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_547_, v_sz_548_, v___x_576_, v___x_574_, v_snd_565_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_snd_560_);
v_a_580_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_562_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_562_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_as_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
size_t v_sz_boxed_598_; size_t v_i_boxed_599_; lean_object* v_res_600_; 
v_sz_boxed_598_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_599_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_588_, v_sz_boxed_598_, v_i_boxed_599_, v_b_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v_as_588_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(lean_object* v_init_601_, lean_object* v_n_602_, lean_object* v_b_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
if (lean_obj_tag(v_n_602_) == 0)
{
lean_object* v_cs_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_664_; 
v_cs_610_ = lean_ctor_get(v_n_602_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_n_602_);
if (v_isSharedCheck_664_ == 0)
{
v___x_612_ = v_n_602_;
v_isShared_613_ = v_isSharedCheck_664_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_cs_610_);
lean_dec(v_n_602_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_664_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; size_t v_sz_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_b_603_);
v_sz_616_ = lean_array_size(v_cs_610_);
v___x_617_ = ((size_t)0ULL);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_601_, v_cs_610_, v_sz_616_, v___x_617_, v___x_615_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec_ref(v_cs_610_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_655_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_655_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_655_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_655_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_fst_623_; lean_object* v_fst_624_; 
v_fst_623_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_fst_623_);
v_fst_624_ = lean_ctor_get(v_fst_623_, 0);
if (lean_obj_tag(v_fst_624_) == 0)
{
lean_object* v_snd_625_; lean_object* v_snd_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_639_; 
v_snd_625_ = lean_ctor_get(v_a_619_, 1);
lean_inc(v_snd_625_);
lean_dec(v_a_619_);
v_snd_626_ = lean_ctor_get(v_fst_623_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_fst_623_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v_fst_623_, 0);
lean_dec(v_unused_640_);
v___x_628_ = v_fst_623_;
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_snd_626_);
lean_dec(v_fst_623_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 1);
lean_ctor_set(v___x_612_, 0, v_snd_626_);
v___x_631_ = v___x_612_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_snd_626_);
v___x_631_ = v_reuseFailAlloc_638_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_snd_625_);
lean_ctor_set(v___x_628_, 0, v___x_631_);
v___x_633_ = v___x_628_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_snd_625_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_633_);
v___x_635_ = v___x_621_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
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
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_652_; 
lean_inc_ref(v_fst_624_);
lean_del_object(v___x_612_);
v_isSharedCheck_652_ = !lean_is_exclusive(v_fst_623_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; 
v_unused_653_ = lean_ctor_get(v_fst_623_, 1);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_fst_623_, 0);
lean_dec(v_unused_654_);
v___x_642_ = v_fst_623_;
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
else
{
lean_dec(v_fst_623_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_snd_644_; lean_object* v_val_645_; lean_object* v___x_647_; 
v_snd_644_ = lean_ctor_get(v_a_619_, 1);
lean_inc(v_snd_644_);
lean_dec(v_a_619_);
v_val_645_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v_fst_624_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_snd_644_);
lean_ctor_set(v___x_642_, 0, v_val_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_val_645_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_644_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_647_);
v___x_649_ = v___x_621_;
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
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_del_object(v___x_612_);
v_a_656_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_618_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_618_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
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
else
{
lean_object* v_vs_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_719_; 
v_vs_665_ = lean_ctor_get(v_n_602_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_n_602_);
if (v_isSharedCheck_719_ == 0)
{
v___x_667_ = v_n_602_;
v_isShared_668_ = v_isSharedCheck_719_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_vs_665_);
lean_dec(v_n_602_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_719_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_b_603_);
v_sz_671_ = lean_array_size(v_vs_665_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_vs_665_, v_sz_671_, v___x_672_, v___x_670_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec_ref(v_vs_665_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_710_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_710_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_710_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_710_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_fst_678_; lean_object* v_fst_679_; 
v_fst_678_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_fst_678_);
v_fst_679_ = lean_ctor_get(v_fst_678_, 0);
if (lean_obj_tag(v_fst_679_) == 0)
{
lean_object* v_snd_680_; lean_object* v_snd_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_694_; 
v_snd_680_ = lean_ctor_get(v_a_674_, 1);
lean_inc(v_snd_680_);
lean_dec(v_a_674_);
v_snd_681_ = lean_ctor_get(v_fst_678_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_fst_678_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_fst_678_, 0);
lean_dec(v_unused_695_);
v___x_683_ = v_fst_678_;
v_isShared_684_ = v_isSharedCheck_694_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_snd_681_);
lean_dec(v_fst_678_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_694_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_snd_681_);
v___x_686_ = v___x_667_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_snd_681_);
v___x_686_ = v_reuseFailAlloc_693_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_688_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v_snd_680_);
lean_ctor_set(v___x_683_, 0, v___x_686_);
v___x_688_ = v___x_683_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_snd_680_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_688_);
v___x_690_ = v___x_676_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
else
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_fst_679_);
lean_del_object(v___x_667_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_fst_678_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_708_ = lean_ctor_get(v_fst_678_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_fst_678_, 0);
lean_dec(v_unused_709_);
v___x_697_ = v_fst_678_;
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_fst_678_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_snd_699_; lean_object* v_val_700_; lean_object* v___x_702_; 
v_snd_699_ = lean_ctor_get(v_a_674_, 1);
lean_inc(v_snd_699_);
lean_dec(v_a_674_);
v_val_700_ = lean_ctor_get(v_fst_679_, 0);
lean_inc(v_val_700_);
lean_dec_ref(v_fst_679_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_snd_699_);
lean_ctor_set(v___x_697_, 0, v_val_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_700_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_699_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_702_);
v___x_704_ = v___x_676_;
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
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_del_object(v___x_667_);
v_a_711_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_673_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_673_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(lean_object* v_init_720_, lean_object* v_as_721_, size_t v_sz_722_, size_t v_i_723_, lean_object* v_b_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_723_, v_sz_722_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_b_724_);
lean_ctor_set(v___x_732_, 1, v___y_725_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_784_; 
v_snd_734_ = lean_ctor_get(v_b_724_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_b_724_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_b_724_, 0);
lean_dec(v_unused_785_);
v___x_736_ = v_b_724_;
v_isShared_737_ = v_isSharedCheck_784_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_dec(v_b_724_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_784_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_a_738_; lean_object* v___x_739_; 
v_a_738_ = lean_array_uget_borrowed(v_as_721_, v_i_723_);
lean_inc(v_snd_734_);
lean_inc(v_a_738_);
v___x_739_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_720_, v_a_738_, v_snd_734_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_775_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_775_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_775_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_775_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_fst_744_; 
v_fst_744_ = lean_ctor_get(v_a_740_, 0);
lean_inc(v_fst_744_);
if (lean_obj_tag(v_fst_744_) == 0)
{
lean_object* v_snd_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_759_; 
v_snd_745_ = lean_ctor_get(v_a_740_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_a_740_, 0);
lean_dec(v_unused_760_);
v___x_747_ = v_a_740_;
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snd_745_);
lean_dec(v_a_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_fst_744_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_snd_734_);
lean_ctor_set(v___x_747_, 0, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_snd_734_);
v___x_751_ = v_reuseFailAlloc_758_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_snd_745_);
lean_ctor_set(v___x_736_, 0, v___x_751_);
v___x_753_ = v___x_736_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_745_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_753_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
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
lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_742_);
lean_del_object(v___x_736_);
lean_dec(v_snd_734_);
v_snd_761_ = lean_ctor_get(v_a_740_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_a_740_, 0);
lean_dec(v_unused_774_);
v___x_763_ = v_a_740_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_dec(v_a_740_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v_a_765_ = lean_ctor_get(v_fst_744_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v_fst_744_);
v___x_766_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v_a_765_);
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_765_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
size_t v___x_769_; size_t v___x_770_; 
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_723_, v___x_769_);
v_i_723_ = v___x_770_;
v_b_724_ = v___x_768_;
v___y_725_ = v_snd_761_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_del_object(v___x_736_);
lean_dec(v_snd_734_);
v_a_776_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_739_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_739_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_init_786_, lean_object* v_as_787_, lean_object* v_sz_788_, lean_object* v_i_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_788_);
lean_dec(v_sz_788_);
v_i_boxed_798_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_786_, v_as_787_, v_sz_boxed_797_, v_i_boxed_798_, v_b_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_as_787_);
lean_dec_ref(v_init_786_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(lean_object* v_init_800_, lean_object* v_n_801_, lean_object* v_b_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_800_, v_n_801_, v_b_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_init_800_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(lean_object* v_t_810_, lean_object* v_init_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_b_819_; lean_object* v___y_820_; lean_object* v_root_823_; lean_object* v_tail_824_; lean_object* v___x_825_; 
v_root_823_ = lean_ctor_get(v_t_810_, 0);
lean_inc_ref(v_root_823_);
v_tail_824_ = lean_ctor_get(v_t_810_, 1);
lean_inc_ref(v_tail_824_);
lean_dec_ref(v_t_810_);
lean_inc_ref(v_init_811_);
v___x_825_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_811_, v_root_823_, v_init_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v_init_811_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v_fst_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref(v___x_825_);
v_fst_827_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_fst_827_);
if (lean_obj_tag(v_fst_827_) == 0)
{
lean_object* v_snd_828_; lean_object* v_a_829_; 
lean_dec_ref(v_tail_824_);
v_snd_828_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_snd_828_);
lean_dec(v_a_826_);
v_a_829_ = lean_ctor_get(v_fst_827_, 0);
lean_inc(v_a_829_);
lean_dec_ref(v_fst_827_);
v_b_819_ = v_a_829_;
v___y_820_ = v_snd_828_;
goto v___jp_818_;
}
else
{
lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_872_; 
v_snd_830_ = lean_ctor_get(v_a_826_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_a_826_, 0);
lean_dec(v_unused_873_);
v___x_832_ = v_a_826_;
v_isShared_833_ = v_isSharedCheck_872_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_dec(v_a_826_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_872_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v_a_834_ = lean_ctor_get(v_fst_827_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v_fst_827_);
v___x_835_ = lean_box(0);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_a_834_);
lean_ctor_set(v___x_832_, 0, v___x_835_);
v___x_837_ = v___x_832_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_834_);
v___x_837_ = v_reuseFailAlloc_871_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
size_t v_sz_838_; size_t v___x_839_; lean_object* v___x_840_; 
v_sz_838_ = lean_array_size(v_tail_824_);
v___x_839_ = ((size_t)0ULL);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_tail_824_, v_sz_838_, v___x_839_, v___x_837_, v_snd_830_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v_tail_824_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_862_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_862_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_862_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_862_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v_fst_845_; lean_object* v_fst_846_; 
v_fst_845_ = lean_ctor_get(v_a_841_, 0);
lean_inc(v_fst_845_);
v_fst_846_ = lean_ctor_get(v_fst_845_, 0);
if (lean_obj_tag(v_fst_846_) == 0)
{
lean_object* v_snd_847_; lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_snd_847_ = lean_ctor_get(v_a_841_, 1);
lean_inc(v_snd_847_);
lean_dec(v_a_841_);
v_snd_848_ = lean_ctor_get(v_fst_845_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_fst_845_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_fst_845_, 0);
lean_dec(v_unused_859_);
v___x_850_ = v_fst_845_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_fst_845_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_snd_847_);
lean_ctor_set(v___x_850_, 0, v_snd_848_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_snd_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_snd_847_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_853_);
v___x_855_ = v___x_843_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_snd_860_; lean_object* v_val_861_; 
lean_inc_ref(v_fst_846_);
lean_dec(v_fst_845_);
lean_del_object(v___x_843_);
v_snd_860_ = lean_ctor_get(v_a_841_, 1);
lean_inc(v_snd_860_);
lean_dec(v_a_841_);
v_val_861_ = lean_ctor_get(v_fst_846_, 0);
lean_inc(v_val_861_);
lean_dec_ref(v_fst_846_);
v_b_819_ = v_val_861_;
v___y_820_ = v_snd_860_;
goto v___jp_818_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_840_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_840_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
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
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref(v_tail_824_);
v_a_874_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_825_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_825_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
v___jp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_b_819_);
lean_ctor_set(v___x_821_, 1, v___y_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1___boxed(lean_object* v_t_882_, lean_object* v_init_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_882_, v_init_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3(void){
_start:
{
lean_object* v___f_895_; lean_object* v___x_896_; 
v___f_895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0));
v___x_896_ = lean_mk_thunk(v___f_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_diseqs_903_; lean_object* v_diseqs_904_; lean_object* v___x_905_; 
v_diseqs_903_ = lean_ctor_get(v_a_897_, 16);
lean_inc_ref(v_diseqs_903_);
v_diseqs_904_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_905_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_diseqs_903_, v_diseqs_904_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_925_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_925_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_925_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_925_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_924_; 
v_fst_910_ = lean_ctor_get(v_a_906_, 0);
v_snd_911_ = lean_ctor_get(v_a_906_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_a_906_);
if (v_isSharedCheck_924_ == 0)
{
v___x_913_ = v_a_906_;
v_isShared_914_ = v_isSharedCheck_924_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snd_911_);
lean_inc(v_fst_910_);
lean_dec(v_a_906_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_924_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2));
v___x_916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3);
v___x_917_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_915_, v___x_916_, v_fst_910_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_917_);
v___x_919_ = v___x_913_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_snd_911_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_919_);
v___x_921_ = v___x_908_;
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
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_905_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_905_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___boxed(lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(lean_object* v_c_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_941_, v___y_942_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(lean_object* v_c_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(lean_object* v_e_957_, lean_object* v_cls_958_){
_start:
{
lean_object* v___x_959_; double v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_959_ = lean_box(0);
v___x_960_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_961_ = 1;
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_963_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_963_, 0, v_cls_958_);
lean_ctor_set(v___x_963_, 1, v___x_959_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
lean_ctor_set_float(v___x_963_, sizeof(void*)*3, v___x_960_);
lean_ctor_set_float(v___x_963_, sizeof(void*)*3 + 8, v___x_960_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*3 + 16, v___x_961_);
v___x_964_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_965_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v_e_957_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(lean_object* v_e_966_, lean_object* v_cls_967_){
_start:
{
lean_object* v___x_968_; double v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_968_ = lean_box(0);
v___x_969_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_970_ = 1;
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_972_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_972_, 0, v_cls_967_);
lean_ctor_set(v___x_972_, 1, v___x_968_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
lean_ctor_set_float(v___x_972_, sizeof(void*)*3, v___x_969_);
lean_ctor_set_float(v___x_972_, sizeof(void*)*3 + 8, v___x_969_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*3 + 16, v___x_970_);
v___x_973_ = l_Lean_stringToMessageData(v_e_966_);
v___x_974_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_975_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_975_, 0, v___x_972_);
lean_ctor_set(v___x_975_, 1, v___x_973_);
lean_ctor_set(v___x_975_, 2, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(lean_object* v___y_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_op_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_op_984_ = lean_ctor_get(v___y_982_, 3);
lean_inc_ref(v_op_984_);
lean_dec_ref(v___y_982_);
v___x_985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1);
v___x_986_ = l_Lean_MessageData_ofExpr(v_op_984_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1));
v___x_994_ = l_Lean_MessageData_ofFormat(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2);
return v___x_996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5(void){
_start:
{
lean_object* v___f_1004_; lean_object* v___x_1005_; 
v___f_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2));
v___x_1005_ = lean_mk_thunk(v___f_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8));
v___x_1012_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10));
v___x_1016_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_1015_, v___x_1014_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12(void){
_start:
{
lean_object* v___x_1017_; lean_object* v_msgs_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11);
v_msgs_1018_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1019_ = lean_array_push(v_msgs_1018_, v___x_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_msgs_1027_; lean_object* v___y_1028_; lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1096_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v_fst_1037_ = lean_ctor_get(v_a_1036_, 0);
v_snd_1038_ = lean_ctor_get(v_a_1036_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1036_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1040_ = v_a_1036_;
v_isShared_1041_ = v_isSharedCheck_1096_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_a_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1096_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_snd_1038_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1095_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1042_);
v_fst_1044_ = lean_ctor_get(v_a_1043_, 0);
v_snd_1045_ = lean_ctor_get(v_a_1043_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1047_ = v_a_1043_;
v_isShared_1048_ = v_isSharedCheck_1095_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_a_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1095_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v_msgs_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v_msgs_1050_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v_msgs_1050_, v_fst_1037_);
v___x_1052_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v___x_1051_, v_fst_1044_);
v___x_1053_ = lean_array_get_size(v___x_1052_);
v___x_1054_ = lean_nat_dec_eq(v___x_1053_, v___x_1049_);
if (v___x_1054_ == 0)
{
lean_object* v_neutral_x3f_1055_; lean_object* v_idempotentInst_x3f_1056_; lean_object* v_commInst_x3f_1057_; lean_object* v_info_1059_; lean_object* v___y_1060_; lean_object* v_info_1066_; lean_object* v___y_1067_; lean_object* v_neutral_x3f_1068_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v_info_1089_; lean_object* v___y_1090_; lean_object* v_neutral_x3f_1091_; lean_object* v_idempotentInst_x3f_1092_; 
v_neutral_x3f_1055_ = lean_ctor_get(v_snd_1045_, 4);
lean_inc(v_neutral_x3f_1055_);
v_idempotentInst_x3f_1056_ = lean_ctor_get(v_snd_1045_, 6);
lean_inc(v_idempotentInst_x3f_1056_);
v_commInst_x3f_1057_ = lean_ctor_get(v_snd_1045_, 7);
if (lean_obj_tag(v_commInst_x3f_1057_) == 0)
{
if (v___x_1054_ == 0)
{
v_info_1089_ = v_msgs_1050_;
v___y_1090_ = v_snd_1045_;
v_neutral_x3f_1091_ = v_neutral_x3f_1055_;
v_idempotentInst_x3f_1092_ = v_idempotentInst_x3f_1056_;
goto v___jp_1088_;
}
else
{
goto v___jp_1093_;
}
}
else
{
goto v___jp_1093_;
}
v___jp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4));
v___x_1062_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5);
v___x_1063_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_1061_, v___x_1062_, v_info_1059_);
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v___x_1052_, v___x_1063_);
v_msgs_1027_ = v___x_1064_;
v___y_1028_ = v___y_1060_;
goto v___jp_1026_;
}
v___jp_1065_:
{
if (lean_obj_tag(v_neutral_x3f_1068_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v_val_1069_ = lean_ctor_get(v_neutral_x3f_1068_, 0);
lean_inc(v_val_1069_);
lean_dec_ref(v_neutral_x3f_1068_);
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7);
v___x_1071_ = l_Lean_MessageData_ofExpr(v_val_1069_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 7);
lean_ctor_set(v___x_1047_, 1, v___x_1071_);
lean_ctor_set(v___x_1047_, 0, v___x_1070_);
v___x_1073_ = v___x_1047_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 7);
lean_ctor_set(v___x_1040_, 1, v___x_1074_);
lean_ctor_set(v___x_1040_, 0, v___x_1073_);
v___x_1076_ = v___x_1040_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1078_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(v___x_1076_, v___x_1077_);
v___x_1079_ = lean_array_push(v_info_1066_, v___x_1078_);
v_info_1059_ = v___x_1079_;
v___y_1060_ = v___y_1067_;
goto v___jp_1058_;
}
}
}
else
{
lean_dec(v_neutral_x3f_1068_);
lean_del_object(v___x_1047_);
lean_del_object(v___x_1040_);
v_info_1059_ = v_info_1066_;
v___y_1060_ = v___y_1067_;
goto v___jp_1058_;
}
}
v___jp_1082_:
{
lean_object* v_neutral_x3f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_neutral_x3f_1085_ = lean_ctor_get(v___y_1083_, 4);
lean_inc(v_neutral_x3f_1085_);
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9);
v___x_1087_ = lean_array_push(v___y_1084_, v___x_1086_);
v_info_1066_ = v___x_1087_;
v___y_1067_ = v___y_1083_;
v_neutral_x3f_1068_ = v_neutral_x3f_1085_;
goto v___jp_1065_;
}
v___jp_1088_:
{
if (lean_obj_tag(v_idempotentInst_x3f_1092_) == 0)
{
if (v___x_1054_ == 0)
{
v_info_1066_ = v_info_1089_;
v___y_1067_ = v___y_1090_;
v_neutral_x3f_1068_ = v_neutral_x3f_1091_;
goto v___jp_1065_;
}
else
{
lean_dec(v_neutral_x3f_1091_);
v___y_1083_ = v___y_1090_;
v___y_1084_ = v_info_1089_;
goto v___jp_1082_;
}
}
else
{
lean_dec_ref(v_idempotentInst_x3f_1092_);
lean_dec(v_neutral_x3f_1091_);
v___y_1083_ = v___y_1090_;
v___y_1084_ = v_info_1089_;
goto v___jp_1082_;
}
}
v___jp_1093_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12);
v_info_1089_ = v___x_1094_;
v___y_1090_ = v_snd_1045_;
v_neutral_x3f_1091_ = v_neutral_x3f_1055_;
v_idempotentInst_x3f_1092_ = v_idempotentInst_x3f_1056_;
goto v___jp_1088_;
}
}
else
{
lean_del_object(v___x_1047_);
lean_del_object(v___x_1040_);
v_msgs_1027_ = v___x_1052_;
v___y_1028_ = v_snd_1045_;
goto v___jp_1026_;
}
}
}
else
{
lean_del_object(v___x_1040_);
lean_dec(v_fst_1037_);
return v___x_1042_;
}
}
}
else
{
return v___x_1035_;
}
v___jp_1026_:
{
lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v___y_1028_);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1029_, 0, v___y_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1));
v___x_1031_ = lean_mk_thunk(v___f_1029_);
v___x_1032_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_1030_, v___x_1031_, v_msgs_1027_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___y_1028_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___boxed(lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(lean_object* v_as_1104_, size_t v_sz_1105_, size_t v_i_1106_, lean_object* v_b_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_a_1114_; uint8_t v___x_1118_; 
v___x_1118_ = lean_usize_dec_lt(v_i_1106_, v_sz_1105_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_b_1107_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_array_uget_borrowed(v_as_1104_, v_i_1106_);
lean_inc(v_a_1120_);
v___x_1121_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1120_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_fst_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
v_fst_1123_ = lean_ctor_get(v_a_1122_, 0);
lean_inc(v_fst_1123_);
lean_dec(v_a_1122_);
if (lean_obj_tag(v_fst_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; 
v_val_1124_ = lean_ctor_get(v_fst_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref(v_fst_1123_);
v___x_1125_ = lean_array_push(v_b_1107_, v_val_1124_);
v_a_1114_ = v___x_1125_;
goto v___jp_1113_;
}
else
{
lean_dec(v_fst_1123_);
v_a_1114_ = v_b_1107_;
goto v___jp_1113_;
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_b_1107_);
v_a_1126_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1121_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1121_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
v___jp_1113_:
{
size_t v___x_1115_; size_t v___x_1116_; 
v___x_1115_ = ((size_t)1ULL);
v___x_1116_ = lean_usize_add(v_i_1106_, v___x_1115_);
v_i_1106_ = v___x_1116_;
v_b_1107_ = v_a_1114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0___boxed(lean_object* v_as_1134_, lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
size_t v_sz_boxed_1143_; size_t v_i_boxed_1144_; lean_object* v_res_1145_; 
v_sz_boxed_1143_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1144_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_1134_, v_sz_boxed_1143_, v_i_boxed_1144_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_as_1134_);
return v_res_1145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0(void){
_start:
{
lean_object* v___x_1146_; uint8_t v___x_1147_; double v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_1147_ = 1;
v___x_1148_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_1149_ = lean_box(0);
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1));
v___x_1151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
lean_ctor_set(v___x_1151_, 2, v___x_1146_);
lean_ctor_set_float(v___x_1151_, sizeof(void*)*3, v___x_1148_);
lean_ctor_set_float(v___x_1151_, sizeof(void*)*3 + 8, v___x_1148_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*3 + 16, v___x_1147_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_Meta_Grind_AC_pp_x3f___closed__2));
v___x_1156_ = l_Lean_MessageData_ofFormat(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f(lean_object* v_goal_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1164_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1163_, v_goal_1157_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_structs_1166_; lean_object* v___x_1167_; lean_object* v_msgs_1168_; size_t v_sz_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
v_structs_1166_ = lean_ctor_get(v_a_1165_, 0);
lean_inc_ref(v_structs_1166_);
lean_dec(v_a_1165_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v_msgs_1168_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v_sz_1169_ = lean_array_size(v_structs_1166_);
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_structs_1166_, v_sz_1169_, v___x_1170_, v_msgs_1168_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec_ref(v_structs_1166_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1196_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1196_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1196_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_array_get_size(v_a_1172_);
v___x_1177_ = lean_nat_dec_eq(v___x_1176_, v___x_1167_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_dec_eq(v___x_1176_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1180_ = lean_obj_once(&l_Lean_Meta_Grind_AC_pp_x3f___closed__0, &l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once, _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0);
v___x_1181_ = lean_obj_once(&l_Lean_Meta_Grind_AC_pp_x3f___closed__3, &l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once, _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3);
v___x_1182_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v_a_1172_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1183_);
v___x_1185_ = v___x_1174_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_array_fget(v_a_1172_, v___x_1167_);
lean_dec(v_a_1172_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1188_);
v___x_1190_ = v___x_1174_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec(v_a_1172_);
v___x_1192_ = lean_box(0);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1192_);
v___x_1194_ = v___x_1174_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1171_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1171_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1217_; 
v_a_1205_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1207_ = v___x_1164_;
v_isShared_1208_ = v_isSharedCheck_1217_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1164_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1217_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_ref_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v_ref_1209_ = lean_ctor_get(v_a_1160_, 5);
v___x_1210_ = lean_io_error_to_string(v_a_1205_);
v___x_1211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
v___x_1212_ = l_Lean_MessageData_ofFormat(v___x_1211_);
lean_inc(v_ref_1209_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_ref_1209_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1213_);
v___x_1215_ = v___x_1207_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f___boxed(lean_object* v_goal_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_Grind_AC_pp_x3f(v_goal_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec_ref(v_goal_1218_);
return v_res_1224_;
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
