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
lean_object* l_instMonadEIO___redArg();
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
v___x_1_ = l_instMonadEIO___redArg();
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
lean_dec_ref_known(v_msg_x3f_78_, 1);
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
lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(lean_object* v_s_100_, lean_object* v___y_101_){
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
lean_dec_ref_known(v_s_100_, 2);
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
LEAN_EXPORT void l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_100_ = stack[0].m_obj;
lean_object* v___y_101_ = stack[1].m_obj;
lean_object* v_res_151_;
v_res_151_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_100_, v___y_101_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_s_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_152_, v___y_153_);
return v_res_155_;
}
}
lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(lean_object* v_c_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_lhs_166_; lean_object* v_rhs_167_; lean_object* v___x_168_; lean_object* v_a_169_; lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_202_; 
v_lhs_166_ = lean_ctor_get(v_c_159_, 0);
lean_inc_ref(v_lhs_166_);
v_rhs_167_ = lean_ctor_get(v_c_159_, 1);
lean_inc_ref(v_rhs_167_);
lean_dec_ref(v_c_159_);
lean_inc_ref(v___y_160_);
v___x_168_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_166_, v___y_160_);
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v___x_168_);
v_fst_170_ = lean_ctor_get(v_a_169_, 0);
v_snd_171_ = lean_ctor_get(v_a_169_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_169_);
if (v_isSharedCheck_202_ == 0)
{
v___x_173_ = v_a_169_;
v_isShared_174_ = v_isSharedCheck_202_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_snd_171_);
lean_inc(v_fst_170_);
lean_dec(v_a_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_202_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_201_; 
v___x_175_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_167_, v_snd_171_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_201_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_200_; 
v_fst_180_ = lean_ctor_get(v_a_176_, 0);
v_snd_181_ = lean_ctor_get(v_a_176_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_200_ == 0)
{
v___x_183_ = v_a_176_;
v_isShared_184_ = v_isSharedCheck_200_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v_a_176_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_200_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_type_185_; lean_object* v_u_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v_type_185_ = lean_ctor_get(v___y_160_, 1);
lean_inc_ref(v_type_185_);
v_u_186_ = lean_ctor_get(v___y_160_, 2);
lean_inc(v_u_186_);
lean_dec_ref(v___y_160_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1));
v___x_188_ = lean_box(0);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 1);
lean_ctor_set(v___x_173_, 1, v___x_188_);
lean_ctor_set(v___x_173_, 0, v_u_186_);
v___x_190_ = v___x_173_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_u_186_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_199_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = l_Lean_mkConst(v___x_187_, v___x_190_);
v___x_192_ = l_Lean_mkApp3(v___x_191_, v_type_185_, v_fst_170_, v_fst_180_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_192_);
v___x_194_ = v___x_183_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_snd_181_);
v___x_194_ = v_reuseFailAlloc_198_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_194_);
v___x_196_ = v___x_178_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_159_ = stack[0].m_obj;
lean_object* v___y_160_ = stack[1].m_obj;
lean_object* v___y_161_ = stack[2].m_obj;
lean_object* v___y_162_ = stack[3].m_obj;
lean_object* v___y_163_ = stack[4].m_obj;
lean_object* v___y_164_ = stack[5].m_obj;
lean_object* v_res_203_;
v_res_203_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___boxed(lean_object* v_c_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(lean_object* v_as_x27_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
if (lean_obj_tag(v_as_x27_216_) == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_b_217_);
lean_ctor_set(v___x_224_, 1, v___y_218_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v_head_226_; lean_object* v_tail_227_; lean_object* v___x_228_; lean_object* v_a_229_; lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_head_226_ = lean_ctor_get(v_as_x27_216_, 0);
v_tail_227_ = lean_ctor_get(v_as_x27_216_, 1);
lean_inc(v_head_226_);
v___x_228_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_head_226_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_228_);
v_fst_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_fst_230_);
v_snd_231_ = lean_ctor_get(v_a_229_, 1);
lean_inc(v_snd_231_);
lean_dec(v_a_229_);
v___x_232_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_233_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_230_, v___x_232_);
v___x_234_ = lean_array_push(v_b_217_, v___x_233_);
v_as_x27_216_ = v_tail_227_;
v_b_217_ = v___x_234_;
v___y_218_ = v_snd_231_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_216_ = stack[0].m_obj;
lean_object* v_b_217_ = stack[1].m_obj;
lean_object* v___y_218_ = stack[2].m_obj;
lean_object* v___y_219_ = stack[3].m_obj;
lean_object* v___y_220_ = stack[4].m_obj;
lean_object* v___y_221_ = stack[5].m_obj;
lean_object* v___y_222_ = stack[6].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_216_, v_b_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___boxed(lean_object* v_as_x27_237_, lean_object* v_b_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_237_, v_b_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v_as_x27_237_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3(void){
_start:
{
lean_object* v___f_250_; lean_object* v___x_251_; 
v___f_250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0));
v___x_251_ = lean_mk_thunk(v___f_250_);
return v___x_251_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_basis_258_; lean_object* v_basis_259_; lean_object* v___x_260_; 
v_basis_258_ = lean_ctor_get(v_a_252_, 15);
lean_inc(v_basis_258_);
v_basis_259_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_260_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_basis_258_, v_basis_259_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
lean_dec(v_basis_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_280_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_280_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_280_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_280_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_fst_265_; lean_object* v_snd_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_279_; 
v_fst_265_ = lean_ctor_get(v_a_261_, 0);
v_snd_266_ = lean_ctor_get(v_a_261_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_a_261_);
if (v_isSharedCheck_279_ == 0)
{
v___x_268_ = v_a_261_;
v_isShared_269_ = v_isSharedCheck_279_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_snd_266_);
lean_inc(v_fst_265_);
lean_dec(v_a_261_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_279_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2));
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3);
v___x_272_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_270_, v___x_271_, v_fst_265_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_272_);
v___x_274_ = v___x_268_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_snd_266_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_274_);
v___x_276_ = v___x_263_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_260_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_260_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_252_ = stack[0].m_obj;
lean_object* v_a_253_ = stack[1].m_obj;
lean_object* v_a_254_ = stack[2].m_obj;
lean_object* v_a_255_ = stack[3].m_obj;
lean_object* v_a_256_ = stack[4].m_obj;
lean_object* v_res_289_;
v_res_289_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___boxed(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
return v_res_296_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(lean_object* v_as_297_, lean_object* v_as_x27_298_, lean_object* v_b_299_, lean_object* v_a_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_298_, v_b_299_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_307_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_297_ = stack[0].m_obj;
lean_object* v_as_x27_298_ = stack[1].m_obj;
lean_object* v_b_299_ = stack[2].m_obj;
lean_object* v___y_301_ = stack[4].m_obj;
lean_object* v___y_302_ = stack[5].m_obj;
lean_object* v___y_303_ = stack[6].m_obj;
lean_object* v___y_304_ = stack[7].m_obj;
lean_object* v___y_305_ = stack[8].m_obj;
lean_object* v_res_308_;
v_res_308_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_297_, v_as_x27_298_, v_b_299_, lean_box(0), v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(lean_object* v_as_309_, lean_object* v_as_x27_310_, lean_object* v_b_311_, lean_object* v_a_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_309_, v_as_x27_310_, v_b_311_, v_a_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v_as_x27_310_);
lean_dec(v_as_309_);
return v_res_319_;
}
}
lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(lean_object* v_s_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_320_, v___y_321_);
return v___x_327_;
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_320_ = stack[0].m_obj;
lean_object* v___y_321_ = stack[1].m_obj;
lean_object* v___y_322_ = stack[2].m_obj;
lean_object* v___y_323_ = stack[3].m_obj;
lean_object* v___y_324_ = stack[4].m_obj;
lean_object* v___y_325_ = stack[5].m_obj;
lean_object* v_res_328_;
v_res_328_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(lean_object* v_s_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1));
v___x_341_ = l_Lean_MessageData_ofFormat(v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2);
return v___x_343_;
}
}
lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(lean_object* v_c_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_lhs_350_; lean_object* v_rhs_351_; lean_object* v___x_352_; lean_object* v_a_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_386_; 
v_lhs_350_ = lean_ctor_get(v_c_347_, 0);
lean_inc_ref(v_lhs_350_);
v_rhs_351_ = lean_ctor_get(v_c_347_, 1);
lean_inc_ref(v_rhs_351_);
lean_dec_ref(v_c_347_);
lean_inc_ref(v___y_348_);
v___x_352_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_350_, v___y_348_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v_fst_354_ = lean_ctor_get(v_a_353_, 0);
v_snd_355_ = lean_ctor_get(v_a_353_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_386_ == 0)
{
v___x_357_ = v_a_353_;
v_isShared_358_ = v_isSharedCheck_386_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snd_355_);
lean_inc(v_fst_354_);
lean_dec(v_a_353_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_386_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_385_; 
v___x_359_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_351_, v_snd_355_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_385_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_385_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_385_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_384_; 
v_fst_364_ = lean_ctor_get(v_a_360_, 0);
v_snd_365_ = lean_ctor_get(v_a_360_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_384_ == 0)
{
v___x_367_ = v_a_360_;
v_isShared_368_ = v_isSharedCheck_384_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_364_);
lean_dec(v_a_360_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_384_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_type_369_; lean_object* v_u_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v_type_369_ = lean_ctor_get(v___y_348_, 1);
lean_inc_ref(v_type_369_);
v_u_370_ = lean_ctor_get(v___y_348_, 2);
lean_inc(v_u_370_);
lean_dec_ref(v___y_348_);
v___x_371_ = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1));
v___x_372_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set_tag(v___x_357_, 1);
lean_ctor_set(v___x_357_, 1, v___x_372_);
lean_ctor_set(v___x_357_, 0, v_u_370_);
v___x_374_ = v___x_357_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_u_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_383_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = l_Lean_mkConst(v___x_371_, v___x_374_);
v___x_376_ = l_Lean_mkApp3(v___x_375_, v_type_369_, v_fst_354_, v_fst_364_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_376_);
v___x_378_ = v___x_367_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_snd_365_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_378_);
v___x_380_ = v___x_362_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_347_ = stack[0].m_obj;
lean_object* v___y_348_ = stack[1].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_347_, v___y_348_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___boxed(lean_object* v_c_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_388_, v___y_389_);
return v_res_391_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(lean_object* v_as_392_, size_t v_sz_393_, size_t v_i_394_, lean_object* v_b_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_usize_dec_lt(v_i_394_, v_sz_393_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_b_395_);
lean_ctor_set(v___x_403_, 1, v___y_396_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_snd_405_; lean_object* v___x_406_; lean_object* v_a_407_; lean_object* v___x_408_; 
v_snd_405_ = lean_ctor_get(v_b_395_, 1);
lean_inc(v_snd_405_);
lean_dec_ref(v_b_395_);
v___x_406_ = lean_box(0);
v_a_407_ = lean_array_uget_borrowed(v_as_392_, v_i_394_);
lean_inc(v_a_407_);
v___x_408_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_407_, v___y_396_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_424_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_fst_410_ = lean_ctor_get(v_a_409_, 0);
v_snd_411_ = lean_ctor_get(v_a_409_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_a_409_);
if (v_isSharedCheck_424_ == 0)
{
v___x_413_ = v_a_409_;
v_isShared_414_ = v_isSharedCheck_424_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_inc(v_fst_410_);
lean_dec(v_a_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_424_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_415_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_416_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_410_, v___x_415_);
v___x_417_ = lean_array_push(v_snd_405_, v___x_416_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_417_);
lean_ctor_set(v___x_413_, 0, v___x_406_);
v___x_419_ = v___x_413_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
size_t v___x_420_; size_t v___x_421_; 
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_394_, v___x_420_);
v_i_394_ = v___x_421_;
v_b_395_ = v___x_419_;
v___y_396_ = v_snd_411_;
goto _start;
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_snd_405_);
v_a_425_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_408_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_408_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_392_ = stack[0].m_obj;
size_t v_sz_393_ = stack[1].m_num;
size_t v_i_394_ = stack[2].m_num;
lean_object* v_b_395_ = stack[3].m_obj;
lean_object* v___y_396_ = stack[4].m_obj;
lean_object* v___y_397_ = stack[5].m_obj;
lean_object* v___y_398_ = stack[6].m_obj;
lean_object* v___y_399_ = stack[7].m_obj;
lean_object* v___y_400_ = stack[8].m_obj;
lean_object* v_res_433_;
v_res_433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_392_, v_sz_393_, v_i_394_, v_b_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_as_434_, lean_object* v_sz_435_, lean_object* v_i_436_, lean_object* v_b_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
size_t v_sz_boxed_444_; size_t v_i_boxed_445_; lean_object* v_res_446_; 
v_sz_boxed_444_ = lean_unbox_usize(v_sz_435_);
lean_dec(v_sz_435_);
v_i_boxed_445_ = lean_unbox_usize(v_i_436_);
lean_dec(v_i_436_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_434_, v_sz_boxed_444_, v_i_boxed_445_, v_b_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v_as_434_);
return v_res_446_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(lean_object* v_as_447_, size_t v_sz_448_, size_t v_i_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_lt(v_i_449_, v_sz_448_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_b_450_);
lean_ctor_set(v___x_458_, 1, v___y_451_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
else
{
lean_object* v_snd_460_; lean_object* v___x_461_; lean_object* v_a_462_; lean_object* v___x_463_; 
v_snd_460_ = lean_ctor_get(v_b_450_, 1);
lean_inc(v_snd_460_);
lean_dec_ref(v_b_450_);
v___x_461_ = lean_box(0);
v_a_462_ = lean_array_uget_borrowed(v_as_447_, v_i_449_);
lean_inc(v_a_462_);
v___x_463_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_462_, v___y_451_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_479_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v_fst_465_ = lean_ctor_get(v_a_464_, 0);
v_snd_466_ = lean_ctor_get(v_a_464_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_464_);
if (v_isSharedCheck_479_ == 0)
{
v___x_468_ = v_a_464_;
v_isShared_469_ = v_isSharedCheck_479_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_465_);
lean_dec(v_a_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_479_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_470_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_471_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_465_, v___x_470_);
v___x_472_ = lean_array_push(v_snd_460_, v___x_471_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_472_);
lean_ctor_set(v___x_468_, 0, v___x_461_);
v___x_474_ = v___x_468_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_add(v_i_449_, v___x_475_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_447_, v_sz_448_, v___x_476_, v___x_474_, v_snd_466_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_snd_460_);
v_a_480_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_463_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_463_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_447_ = stack[0].m_obj;
size_t v_sz_448_ = stack[1].m_num;
size_t v_i_449_ = stack[2].m_num;
lean_object* v_b_450_ = stack[3].m_obj;
lean_object* v___y_451_ = stack[4].m_obj;
lean_object* v___y_452_ = stack[5].m_obj;
lean_object* v___y_453_ = stack[6].m_obj;
lean_object* v___y_454_ = stack[7].m_obj;
lean_object* v___y_455_ = stack[8].m_obj;
lean_object* v_res_488_;
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_447_, v_sz_448_, v_i_449_, v_b_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2___boxed(lean_object* v_as_489_, lean_object* v_sz_490_, lean_object* v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_490_);
lean_dec(v_sz_490_);
v_i_boxed_500_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_489_, v_sz_boxed_499_, v_i_boxed_500_, v_b_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec_ref(v_as_489_);
return v_res_501_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_502_, size_t v_sz_503_, size_t v_i_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_504_, v_sz_503_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_b_505_);
lean_ctor_set(v___x_513_, 1, v___y_506_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_snd_515_; lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_518_; 
v_snd_515_ = lean_ctor_get(v_b_505_, 1);
lean_inc(v_snd_515_);
lean_dec_ref(v_b_505_);
v___x_516_ = lean_box(0);
v_a_517_ = lean_array_uget_borrowed(v_as_502_, v_i_504_);
lean_inc(v_a_517_);
v___x_518_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_517_, v___y_506_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_534_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v_fst_520_ = lean_ctor_get(v_a_519_, 0);
v_snd_521_ = lean_ctor_get(v_a_519_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_a_519_);
if (v_isSharedCheck_534_ == 0)
{
v___x_523_ = v_a_519_;
v_isShared_524_ = v_isSharedCheck_534_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_snd_521_);
lean_inc(v_fst_520_);
lean_dec(v_a_519_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_534_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_526_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_520_, v___x_525_);
v___x_527_ = lean_array_push(v_snd_515_, v___x_526_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_527_);
lean_ctor_set(v___x_523_, 0, v___x_516_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
size_t v___x_530_; size_t v___x_531_; 
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_504_, v___x_530_);
v_i_504_ = v___x_531_;
v_b_505_ = v___x_529_;
v___y_506_ = v_snd_521_;
goto _start;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_snd_515_);
v_a_535_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_518_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_518_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_502_ = stack[0].m_obj;
size_t v_sz_503_ = stack[1].m_num;
size_t v_i_504_ = stack[2].m_num;
lean_object* v_b_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v___y_509_ = stack[7].m_obj;
lean_object* v___y_510_ = stack[8].m_obj;
lean_object* v_res_543_;
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_502_, v_sz_503_, v_i_504_, v_b_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_544_, lean_object* v_sz_545_, lean_object* v_i_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
size_t v_sz_boxed_554_; size_t v_i_boxed_555_; lean_object* v_res_556_; 
v_sz_boxed_554_ = lean_unbox_usize(v_sz_545_);
lean_dec(v_sz_545_);
v_i_boxed_555_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_544_, v_sz_boxed_554_, v_i_boxed_555_, v_b_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec_ref(v_as_544_);
return v_res_556_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(lean_object* v_as_557_, size_t v_sz_558_, size_t v_i_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = lean_usize_dec_lt(v_i_559_, v_sz_558_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_b_560_);
lean_ctor_set(v___x_568_, 1, v___y_561_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v_snd_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_573_; 
v_snd_570_ = lean_ctor_get(v_b_560_, 1);
lean_inc(v_snd_570_);
lean_dec_ref(v_b_560_);
v___x_571_ = lean_box(0);
v_a_572_ = lean_array_uget_borrowed(v_as_557_, v_i_559_);
lean_inc(v_a_572_);
v___x_573_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_572_, v___y_561_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_589_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v_fst_575_ = lean_ctor_get(v_a_574_, 0);
v_snd_576_ = lean_ctor_get(v_a_574_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_a_574_);
if (v_isSharedCheck_589_ == 0)
{
v___x_578_ = v_a_574_;
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
lean_dec(v_a_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_580_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_581_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_575_, v___x_580_);
v___x_582_ = lean_array_push(v_snd_570_, v___x_581_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___x_582_);
lean_ctor_set(v___x_578_, 0, v___x_571_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_559_, v___x_585_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_557_, v_sz_558_, v___x_586_, v___x_584_, v_snd_576_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_snd_570_);
v_a_590_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_573_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_573_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_557_ = stack[0].m_obj;
size_t v_sz_558_ = stack[1].m_num;
size_t v_i_559_ = stack[2].m_num;
lean_object* v_b_560_ = stack[3].m_obj;
lean_object* v___y_561_ = stack[4].m_obj;
lean_object* v___y_562_ = stack[5].m_obj;
lean_object* v___y_563_ = stack[6].m_obj;
lean_object* v___y_564_ = stack[7].m_obj;
lean_object* v___y_565_ = stack[8].m_obj;
lean_object* v_res_598_;
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_557_, v_sz_558_, v_i_559_, v_b_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_as_599_, lean_object* v_sz_600_, lean_object* v_i_601_, lean_object* v_b_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
size_t v_sz_boxed_609_; size_t v_i_boxed_610_; lean_object* v_res_611_; 
v_sz_boxed_609_ = lean_unbox_usize(v_sz_600_);
lean_dec(v_sz_600_);
v_i_boxed_610_ = lean_unbox_usize(v_i_601_);
lean_dec(v_i_601_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_599_, v_sz_boxed_609_, v_i_boxed_610_, v_b_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec_ref(v_as_599_);
return v_res_611_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(lean_object* v_init_612_, lean_object* v_n_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
if (lean_obj_tag(v_n_613_) == 0)
{
lean_object* v_cs_621_; lean_object* v___x_622_; lean_object* v___x_623_; size_t v_sz_624_; size_t v___x_625_; lean_object* v___x_626_; 
v_cs_621_ = lean_ctor_get(v_n_613_, 0);
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v_b_614_);
v_sz_624_ = lean_array_size(v_cs_621_);
v___x_625_ = ((size_t)0ULL);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_612_, v_cs_621_, v_sz_624_, v___x_625_, v___x_623_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_661_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_661_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_661_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_661_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_fst_631_; lean_object* v_fst_632_; 
v_fst_631_ = lean_ctor_get(v_a_627_, 0);
lean_inc(v_fst_631_);
v_fst_632_ = lean_ctor_get(v_fst_631_, 0);
if (lean_obj_tag(v_fst_632_) == 0)
{
lean_object* v_snd_633_; lean_object* v_snd_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_snd_633_ = lean_ctor_get(v_a_627_, 1);
lean_inc(v_snd_633_);
lean_dec(v_a_627_);
v_snd_634_ = lean_ctor_get(v_fst_631_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_fst_631_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_fst_631_, 0);
lean_dec(v_unused_646_);
v___x_636_ = v_fst_631_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_snd_634_);
lean_dec(v_fst_631_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_snd_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_snd_633_);
lean_ctor_set(v___x_636_, 0, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_snd_633_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_640_);
v___x_642_ = v___x_629_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_658_; 
lean_inc_ref(v_fst_632_);
v_isSharedCheck_658_ = !lean_is_exclusive(v_fst_631_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_659_ = lean_ctor_get(v_fst_631_, 1);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_fst_631_, 0);
lean_dec(v_unused_660_);
v___x_648_ = v_fst_631_;
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_fst_631_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_snd_650_; lean_object* v_val_651_; lean_object* v___x_653_; 
v_snd_650_ = lean_ctor_get(v_a_627_, 1);
lean_inc(v_snd_650_);
lean_dec(v_a_627_);
v_val_651_ = lean_ctor_get(v_fst_632_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v_fst_632_, 1);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_snd_650_);
lean_ctor_set(v___x_648_, 0, v_val_651_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_val_651_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_snd_650_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_653_);
v___x_655_ = v___x_629_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
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
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_626_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_626_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_vs_670_; lean_object* v___x_671_; lean_object* v___x_672_; size_t v_sz_673_; size_t v___x_674_; lean_object* v___x_675_; 
v_vs_670_ = lean_ctor_get(v_n_613_, 0);
v___x_671_ = lean_box(0);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_b_614_);
v_sz_673_ = lean_array_size(v_vs_670_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_vs_670_, v_sz_673_, v___x_674_, v___x_672_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_710_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_710_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_710_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_710_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_fst_680_; lean_object* v_fst_681_; 
v_fst_680_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_fst_680_);
v_fst_681_ = lean_ctor_get(v_fst_680_, 0);
if (lean_obj_tag(v_fst_681_) == 0)
{
lean_object* v_snd_682_; lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_694_; 
v_snd_682_ = lean_ctor_get(v_a_676_, 1);
lean_inc(v_snd_682_);
lean_dec(v_a_676_);
v_snd_683_ = lean_ctor_get(v_fst_680_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_fst_680_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_fst_680_, 0);
lean_dec(v_unused_695_);
v___x_685_ = v_fst_680_;
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_dec(v_fst_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_snd_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_snd_682_);
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_snd_682_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_689_);
v___x_691_ = v___x_678_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
else
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_fst_681_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_fst_680_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_708_ = lean_ctor_get(v_fst_680_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_fst_680_, 0);
lean_dec(v_unused_709_);
v___x_697_ = v_fst_680_;
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_fst_680_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_snd_699_; lean_object* v_val_700_; lean_object* v___x_702_; 
v_snd_699_ = lean_ctor_get(v_a_676_, 1);
lean_inc(v_snd_699_);
lean_dec(v_a_676_);
v_val_700_ = lean_ctor_get(v_fst_681_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_fst_681_, 1);
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
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_702_);
v___x_704_ = v___x_678_;
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
v_a_711_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_675_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_675_);
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
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_612_ = stack[0].m_obj;
lean_object* v_n_613_ = stack[1].m_obj;
lean_object* v_b_614_ = stack[2].m_obj;
lean_object* v___y_615_ = stack[3].m_obj;
lean_object* v___y_616_ = stack[4].m_obj;
lean_object* v___y_617_ = stack[5].m_obj;
lean_object* v___y_618_ = stack[6].m_obj;
lean_object* v___y_619_ = stack[7].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_612_, v_n_613_, v_b_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
stack->m_obj
 = v_res_719_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(lean_object* v_init_720_, lean_object* v_as_721_, size_t v_sz_722_, size_t v_i_723_, lean_object* v_b_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
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
lean_object* v___x_738_; lean_object* v_a_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v_a_739_ = lean_array_uget_borrowed(v_as_721_, v_i_723_);
lean_inc(v_snd_734_);
v___x_740_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_720_, v_a_739_, v_snd_734_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_775_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_775_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_775_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_775_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_fst_745_; 
v_fst_745_ = lean_ctor_get(v_a_741_, 0);
lean_inc(v_fst_745_);
if (lean_obj_tag(v_fst_745_) == 0)
{
lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
v_snd_746_ = lean_ctor_get(v_a_741_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v_a_741_, 0);
lean_dec(v_unused_761_);
v___x_748_ = v_a_741_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_dec(v_a_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v_fst_745_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_snd_734_);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_734_);
v___x_752_ = v_reuseFailAlloc_759_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_snd_746_);
lean_ctor_set(v___x_736_, 0, v___x_752_);
v___x_754_ = v___x_736_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_snd_746_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_754_);
v___x_756_ = v___x_743_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
else
{
lean_object* v_snd_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_743_);
lean_del_object(v___x_736_);
lean_dec(v_snd_734_);
v_snd_762_ = lean_ctor_get(v_a_741_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_a_741_, 0);
lean_dec(v_unused_774_);
v___x_764_ = v_a_741_;
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_snd_762_);
lean_dec(v_a_741_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_a_766_; lean_object* v___x_768_; 
v_a_766_ = lean_ctor_get(v_fst_745_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v_fst_745_, 1);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v_a_766_);
lean_ctor_set(v___x_764_, 0, v___x_738_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
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
v___y_725_ = v_snd_762_;
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
v_a_776_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_740_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_740_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_720_ = stack[0].m_obj;
lean_object* v_as_721_ = stack[1].m_obj;
size_t v_sz_722_ = stack[2].m_num;
size_t v_i_723_ = stack[3].m_num;
lean_object* v_b_724_ = stack[4].m_obj;
lean_object* v___y_725_ = stack[5].m_obj;
lean_object* v___y_726_ = stack[6].m_obj;
lean_object* v___y_727_ = stack[7].m_obj;
lean_object* v___y_728_ = stack[8].m_obj;
lean_object* v___y_729_ = stack[9].m_obj;
lean_object* v_res_786_;
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_720_, v_as_721_, v_sz_722_, v_i_723_, v_b_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_init_787_, lean_object* v_as_788_, lean_object* v_sz_789_, lean_object* v_i_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
size_t v_sz_boxed_798_; size_t v_i_boxed_799_; lean_object* v_res_800_; 
v_sz_boxed_798_ = lean_unbox_usize(v_sz_789_);
lean_dec(v_sz_789_);
v_i_boxed_799_ = lean_unbox_usize(v_i_790_);
lean_dec(v_i_790_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_787_, v_as_788_, v_sz_boxed_798_, v_i_boxed_799_, v_b_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_as_788_);
lean_dec_ref(v_init_787_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(lean_object* v_init_801_, lean_object* v_n_802_, lean_object* v_b_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_801_, v_n_802_, v_b_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_n_802_);
lean_dec_ref(v_init_801_);
return v_res_810_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(lean_object* v_t_811_, lean_object* v_init_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_b_820_; lean_object* v___y_821_; lean_object* v_root_824_; lean_object* v_tail_825_; lean_object* v___x_826_; 
v_root_824_ = lean_ctor_get(v_t_811_, 0);
v_tail_825_ = lean_ctor_get(v_t_811_, 1);
lean_inc_ref(v_init_812_);
v___x_826_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_812_, v_root_824_, v_init_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec_ref(v_init_812_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_fst_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v_fst_828_ = lean_ctor_get(v_a_827_, 0);
lean_inc(v_fst_828_);
if (lean_obj_tag(v_fst_828_) == 0)
{
lean_object* v_snd_829_; lean_object* v_a_830_; 
v_snd_829_ = lean_ctor_get(v_a_827_, 1);
lean_inc(v_snd_829_);
lean_dec(v_a_827_);
v_a_830_ = lean_ctor_get(v_fst_828_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v_fst_828_, 1);
v_b_820_ = v_a_830_;
v___y_821_ = v_snd_829_;
goto v___jp_819_;
}
else
{
lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_873_; 
v_snd_831_ = lean_ctor_get(v_a_827_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_a_827_, 0);
lean_dec(v_unused_874_);
v___x_833_ = v_a_827_;
v_isShared_834_ = v_isSharedCheck_873_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_dec(v_a_827_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_873_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_a_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v_a_835_ = lean_ctor_get(v_fst_828_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v_fst_828_, 1);
v___x_836_ = lean_box(0);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_a_835_);
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_a_835_);
v___x_838_ = v_reuseFailAlloc_872_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
size_t v_sz_839_; size_t v___x_840_; lean_object* v___x_841_; 
v_sz_839_ = lean_array_size(v_tail_825_);
v___x_840_ = ((size_t)0ULL);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_tail_825_, v_sz_839_, v___x_840_, v___x_838_, v_snd_831_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_863_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_863_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_863_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_863_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v_fst_847_; 
v_fst_846_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_fst_846_);
v_fst_847_ = lean_ctor_get(v_fst_846_, 0);
if (lean_obj_tag(v_fst_847_) == 0)
{
lean_object* v_snd_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_859_; 
v_snd_848_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_842_);
v_snd_849_ = lean_ctor_get(v_fst_846_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_fst_846_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v_fst_846_, 0);
lean_dec(v_unused_860_);
v___x_851_ = v_fst_846_;
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_dec(v_fst_846_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_snd_848_);
lean_ctor_set(v___x_851_, 0, v_snd_849_);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_snd_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_snd_848_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_854_);
v___x_856_ = v___x_844_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_snd_861_; lean_object* v_val_862_; 
lean_inc_ref(v_fst_847_);
lean_dec(v_fst_846_);
lean_del_object(v___x_844_);
v_snd_861_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_861_);
lean_dec(v_a_842_);
v_val_862_ = lean_ctor_get(v_fst_847_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_fst_847_, 1);
v_b_820_ = v_val_862_;
v___y_821_ = v_snd_861_;
goto v___jp_819_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_841_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_841_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
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
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_826_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_826_);
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
v___jp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_b_820_);
lean_ctor_set(v___x_822_, 1, v___y_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_811_ = stack[0].m_obj;
lean_object* v_init_812_ = stack[1].m_obj;
lean_object* v___y_813_ = stack[2].m_obj;
lean_object* v___y_814_ = stack[3].m_obj;
lean_object* v___y_815_ = stack[4].m_obj;
lean_object* v___y_816_ = stack[5].m_obj;
lean_object* v___y_817_ = stack[6].m_obj;
lean_object* v_res_883_;
v_res_883_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_811_, v_init_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1___boxed(lean_object* v_t_884_, lean_object* v_init_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_884_, v_init_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec_ref(v_t_884_);
return v_res_892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3(void){
_start:
{
lean_object* v___f_897_; lean_object* v___x_898_; 
v___f_897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0));
v___x_898_ = lean_mk_thunk(v___f_897_);
return v___x_898_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_diseqs_905_; lean_object* v_diseqs_906_; lean_object* v___x_907_; 
v_diseqs_905_ = lean_ctor_get(v_a_899_, 16);
lean_inc_ref(v_diseqs_905_);
v_diseqs_906_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_907_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_diseqs_905_, v_diseqs_906_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec_ref(v_diseqs_905_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_927_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_927_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_927_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_927_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_926_; 
v_fst_912_ = lean_ctor_get(v_a_908_, 0);
v_snd_913_ = lean_ctor_get(v_a_908_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_908_);
if (v_isSharedCheck_926_ == 0)
{
v___x_915_ = v_a_908_;
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snd_913_);
lean_inc(v_fst_912_);
lean_dec(v_a_908_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2));
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3);
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_917_, v___x_918_, v_fst_912_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_919_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_snd_913_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_921_);
v___x_923_ = v___x_910_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_907_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_907_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_899_ = stack[0].m_obj;
lean_object* v_a_900_ = stack[1].m_obj;
lean_object* v_a_901_ = stack[2].m_obj;
lean_object* v_a_902_ = stack[3].m_obj;
lean_object* v_a_903_ = stack[4].m_obj;
lean_object* v_res_936_;
v_res_936_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___boxed(lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_943_;
}
}
lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(lean_object* v_c_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_944_, v___y_945_);
return v___x_951_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_944_ = stack[0].m_obj;
lean_object* v___y_945_ = stack[1].m_obj;
lean_object* v___y_946_ = stack[2].m_obj;
lean_object* v___y_947_ = stack[3].m_obj;
lean_object* v___y_948_ = stack[4].m_obj;
lean_object* v___y_949_ = stack[5].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(lean_object* v_c_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(lean_object* v_e_961_, lean_object* v_cls_962_){
_start:
{
lean_object* v___x_963_; double v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_963_ = lean_box(0);
v___x_964_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_965_ = 1;
v___x_966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_967_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_967_, 0, v_cls_962_);
lean_ctor_set(v___x_967_, 1, v___x_963_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
lean_ctor_set_float(v___x_967_, sizeof(void*)*3, v___x_964_);
lean_ctor_set_float(v___x_967_, sizeof(void*)*3 + 8, v___x_964_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*3 + 16, v___x_965_);
v___x_968_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_969_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v_e_961_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(lean_object* v_e_970_, lean_object* v_cls_971_){
_start:
{
lean_object* v___x_972_; double v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_972_ = lean_box(0);
v___x_973_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_974_ = 1;
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_976_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_976_, 0, v_cls_971_);
lean_ctor_set(v___x_976_, 1, v___x_972_);
lean_ctor_set(v___x_976_, 2, v___x_975_);
lean_ctor_set_float(v___x_976_, sizeof(void*)*3, v___x_973_);
lean_ctor_set_float(v___x_976_, sizeof(void*)*3 + 8, v___x_973_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*3 + 16, v___x_974_);
v___x_977_ = l_Lean_stringToMessageData(v_e_970_);
v___x_978_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_979_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_979_, 0, v___x_976_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(lean_object* v___y_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_op_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_op_988_ = lean_ctor_get(v___y_986_, 3);
lean_inc_ref(v_op_988_);
lean_dec_ref(v___y_986_);
v___x_989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1);
v___x_990_ = l_Lean_MessageData_ofExpr(v_op_988_);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1));
v___x_998_ = l_Lean_MessageData_ofFormat(v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(lean_object* v_x_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5(void){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; 
v___f_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2));
v___x_1009_ = lean_mk_thunk(v___f_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8));
v___x_1016_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_1015_, v___x_1014_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10));
v___x_1020_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12(void){
_start:
{
lean_object* v___x_1021_; lean_object* v_msgs_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11);
v_msgs_1022_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1023_ = lean_array_push(v_msgs_1022_, v___x_1021_);
return v___x_1023_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_msgs_1031_; lean_object* v___y_1032_; lean_object* v___x_1039_; lean_object* v_msgs_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v_msgs_1040_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1041_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_fst_1043_; lean_object* v_snd_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1097_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v_fst_1043_ = lean_ctor_get(v_a_1042_, 0);
v_snd_1044_ = lean_ctor_get(v_a_1042_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1042_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1046_ = v_a_1042_;
v_isShared_1047_ = v_isSharedCheck_1097_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_snd_1044_);
lean_inc(v_fst_1043_);
lean_dec(v_a_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1097_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v_msgs_1040_, v_fst_1043_);
v___x_1049_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(v_snd_1044_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1096_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v_fst_1051_ = lean_ctor_get(v_a_1050_, 0);
v_snd_1052_ = lean_ctor_get(v_a_1050_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1050_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1054_ = v_a_1050_;
v_isShared_1055_ = v_isSharedCheck_1096_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v_a_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1096_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v_info_1058_; lean_object* v___y_1059_; lean_object* v_info_1065_; lean_object* v___y_1066_; lean_object* v_neutral_x3f_1067_; lean_object* v_info_1082_; lean_object* v___y_1083_; lean_object* v_neutral_x3f_1084_; lean_object* v_idempotentInst_x3f_1085_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1056_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v___x_1048_, v_fst_1051_);
v___x_1088_ = lean_array_get_size(v___x_1056_);
v___x_1089_ = lean_nat_dec_eq(v___x_1088_, v___x_1039_);
if (v___x_1089_ == 0)
{
lean_object* v_commInst_x3f_1090_; 
v_commInst_x3f_1090_ = lean_ctor_get(v_snd_1052_, 7);
if (lean_obj_tag(v_commInst_x3f_1090_) == 0)
{
lean_object* v_neutral_x3f_1091_; lean_object* v_idempotentInst_x3f_1092_; 
v_neutral_x3f_1091_ = lean_ctor_get(v_snd_1052_, 4);
lean_inc(v_neutral_x3f_1091_);
v_idempotentInst_x3f_1092_ = lean_ctor_get(v_snd_1052_, 6);
lean_inc(v_idempotentInst_x3f_1092_);
v_info_1082_ = v_msgs_1040_;
v___y_1083_ = v_snd_1052_;
v_neutral_x3f_1084_ = v_neutral_x3f_1091_;
v_idempotentInst_x3f_1085_ = v_idempotentInst_x3f_1092_;
goto v___jp_1081_;
}
else
{
lean_object* v_neutral_x3f_1093_; lean_object* v_idempotentInst_x3f_1094_; lean_object* v___x_1095_; 
v_neutral_x3f_1093_ = lean_ctor_get(v_snd_1052_, 4);
lean_inc(v_neutral_x3f_1093_);
v_idempotentInst_x3f_1094_ = lean_ctor_get(v_snd_1052_, 6);
lean_inc(v_idempotentInst_x3f_1094_);
v___x_1095_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12);
v_info_1082_ = v___x_1095_;
v___y_1083_ = v_snd_1052_;
v_neutral_x3f_1084_ = v_neutral_x3f_1093_;
v_idempotentInst_x3f_1085_ = v_idempotentInst_x3f_1094_;
goto v___jp_1081_;
}
}
else
{
lean_del_object(v___x_1054_);
lean_del_object(v___x_1046_);
v_msgs_1031_ = v___x_1056_;
v___y_1032_ = v_snd_1052_;
goto v___jp_1030_;
}
v___jp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4));
v___x_1061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5);
v___x_1062_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_1060_, v___x_1061_, v_info_1058_);
v___x_1063_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(v___x_1056_, v___x_1062_);
v_msgs_1031_ = v___x_1063_;
v___y_1032_ = v___y_1059_;
goto v___jp_1030_;
}
v___jp_1064_:
{
if (lean_obj_tag(v_neutral_x3f_1067_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_val_1068_ = lean_ctor_get(v_neutral_x3f_1067_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_neutral_x3f_1067_, 1);
v___x_1069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7);
v___x_1070_ = l_Lean_MessageData_ofExpr(v_val_1068_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 7);
lean_ctor_set(v___x_1054_, 1, v___x_1070_);
lean_ctor_set(v___x_1054_, 0, v___x_1069_);
v___x_1072_ = v___x_1054_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 7);
lean_ctor_set(v___x_1046_, 1, v___x_1073_);
lean_ctor_set(v___x_1046_, 0, v___x_1072_);
v___x_1075_ = v___x_1046_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1));
v___x_1077_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(v___x_1075_, v___x_1076_);
v___x_1078_ = lean_array_push(v_info_1065_, v___x_1077_);
v_info_1058_ = v___x_1078_;
v___y_1059_ = v___y_1066_;
goto v___jp_1057_;
}
}
}
else
{
lean_dec(v_neutral_x3f_1067_);
lean_del_object(v___x_1054_);
lean_del_object(v___x_1046_);
v_info_1058_ = v_info_1065_;
v___y_1059_ = v___y_1066_;
goto v___jp_1057_;
}
}
v___jp_1081_:
{
if (lean_obj_tag(v_idempotentInst_x3f_1085_) == 0)
{
v_info_1065_ = v_info_1082_;
v___y_1066_ = v___y_1083_;
v_neutral_x3f_1067_ = v_neutral_x3f_1084_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref_known(v_idempotentInst_x3f_1085_, 1);
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9);
v___x_1087_ = lean_array_push(v_info_1082_, v___x_1086_);
v_info_1065_ = v___x_1087_;
v___y_1066_ = v___y_1083_;
v_neutral_x3f_1067_ = v_neutral_x3f_1084_;
goto v___jp_1064_;
}
}
}
}
else
{
lean_dec_ref(v___x_1048_);
lean_del_object(v___x_1046_);
return v___x_1049_;
}
}
}
else
{
return v___x_1041_;
}
v___jp_1030_:
{
lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_inc_ref(v___y_1032_);
v___f_1033_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1033_, 0, v___y_1032_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1));
v___x_1035_ = lean_mk_thunk(v___f_1033_);
v___x_1036_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(v___x_1034_, v___x_1035_, v_msgs_1031_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___y_1032_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1024_ = stack[0].m_obj;
lean_object* v_a_1025_ = stack[1].m_obj;
lean_object* v_a_1026_ = stack[2].m_obj;
lean_object* v_a_1027_ = stack[3].m_obj;
lean_object* v_a_1028_ = stack[4].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___boxed(lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1105_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(lean_object* v_as_1106_, size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_a_1116_; uint8_t v___x_1120_; 
v___x_1120_ = lean_usize_dec_lt(v_i_1108_, v_sz_1107_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_b_1109_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
v_a_1122_ = lean_array_uget_borrowed(v_as_1106_, v_i_1108_);
lean_inc(v_a_1122_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(v_a_1122_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v_fst_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v_fst_1125_ = lean_ctor_get(v_a_1124_, 0);
lean_inc(v_fst_1125_);
lean_dec(v_a_1124_);
if (lean_obj_tag(v_fst_1125_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1127_; 
v_val_1126_ = lean_ctor_get(v_fst_1125_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v_fst_1125_, 1);
v___x_1127_ = lean_array_push(v_b_1109_, v_val_1126_);
v_a_1116_ = v___x_1127_;
goto v___jp_1115_;
}
else
{
lean_dec(v_fst_1125_);
v_a_1116_ = v_b_1109_;
goto v___jp_1115_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_b_1109_);
v_a_1128_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1123_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1123_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
v___jp_1115_:
{
size_t v___x_1117_; size_t v___x_1118_; 
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_add(v_i_1108_, v___x_1117_);
v_i_1108_ = v___x_1118_;
v_b_1109_ = v_a_1116_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1106_ = stack[0].m_obj;
size_t v_sz_1107_ = stack[1].m_num;
size_t v_i_1108_ = stack[2].m_num;
lean_object* v_b_1109_ = stack[3].m_obj;
lean_object* v___y_1110_ = stack[4].m_obj;
lean_object* v___y_1111_ = stack[5].m_obj;
lean_object* v___y_1112_ = stack[6].m_obj;
lean_object* v___y_1113_ = stack[7].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_1106_, v_sz_1107_, v_i_1108_, v_b_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0___boxed(lean_object* v_as_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_1137_, v_sz_boxed_1146_, v_i_boxed_1147_, v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_as_1137_);
return v_res_1148_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0(void){
_start:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; double v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1));
v___x_1150_ = 1;
v___x_1151_ = lean_float_once(&l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
v___x_1152_ = lean_box(0);
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1));
v___x_1154_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
lean_ctor_set(v___x_1154_, 2, v___x_1149_);
lean_ctor_set_float(v___x_1154_, sizeof(void*)*3, v___x_1151_);
lean_ctor_set_float(v___x_1154_, sizeof(void*)*3 + 8, v___x_1151_);
lean_ctor_set_uint8(v___x_1154_, sizeof(void*)*3 + 16, v___x_1150_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_Meta_Grind_AC_pp_x3f___closed__2));
v___x_1159_ = l_Lean_MessageData_ofFormat(v___x_1158_);
return v___x_1159_;
}
}
lean_object* l_Lean_Meta_Grind_AC_pp_x3f(lean_object* v_goal_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_ref_1166_; lean_object* v___x_1167_; lean_object* v_msgs_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_ref_1166_ = lean_ctor_get(v_a_1163_, 2);
v___x_1167_ = lean_unsigned_to_nat(0u);
v_msgs_1168_ = ((lean_object*)(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0));
v___x_1169_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1170_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1169_, v_goal_1160_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_structs_1172_; size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v_structs_1172_ = lean_ctor_get(v_a_1171_, 0);
lean_inc_ref(v_structs_1172_);
lean_dec(v_a_1171_);
v_sz_1173_ = lean_array_size(v_structs_1172_);
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_structs_1172_, v_sz_1173_, v___x_1174_, v_msgs_1168_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec_ref(v_structs_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1200_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_a_1176_);
v___x_1181_ = lean_nat_dec_eq(v___x_1180_, v___x_1167_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_nat_dec_eq(v___x_1180_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1184_ = lean_obj_once(&l_Lean_Meta_Grind_AC_pp_x3f___closed__0, &l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once, _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0);
v___x_1185_ = lean_obj_once(&l_Lean_Meta_Grind_AC_pp_x3f___closed__3, &l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once, _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3);
v___x_1186_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
lean_ctor_set(v___x_1186_, 2, v_a_1176_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1187_);
v___x_1189_ = v___x_1178_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = lean_array_fget(v_a_1176_, v___x_1167_);
lean_dec(v_a_1176_);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1192_);
v___x_1194_ = v___x_1178_;
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
else
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_dec(v_a_1176_);
v___x_1196_ = lean_box(0);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1196_);
v___x_1198_ = v___x_1178_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1175_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1175_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1220_; 
v_a_1209_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1211_ = v___x_1170_;
v_isShared_1212_ = v_isSharedCheck_1220_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1170_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1220_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1213_ = lean_io_error_to_string(v_a_1209_);
v___x_1214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = l_Lean_MessageData_ofFormat(v___x_1214_);
lean_inc(v_ref_1166_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_ref_1166_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1216_);
v___x_1218_ = v___x_1211_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_pp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1160_ = stack[0].m_obj;
lean_object* v_a_1161_ = stack[1].m_obj;
lean_object* v_a_1162_ = stack[2].m_obj;
lean_object* v_a_1163_ = stack[3].m_obj;
lean_object* v_a_1164_ = stack[4].m_obj;
lean_object* v_res_1221_;
v_res_1221_ = l_Lean_Meta_Grind_AC_pp_x3f(v_goal_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
stack->m_obj
 = v_res_1221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_pp_x3f___boxed(lean_object* v_goal_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Meta_Grind_AC_pp_x3f(v_goal_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec_ref(v_goal_1222_);
return v_res_1228_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
