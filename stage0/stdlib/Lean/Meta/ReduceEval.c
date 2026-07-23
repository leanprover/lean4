// Lean compiler output
// Module: Lean.Meta.ReduceEval
// Imports: public import Lean.Meta.Offset
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
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "reduceEval: failed to evaluate argument"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalNat___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalNat___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalNat = (const lean_object*)&l_Lean_Meta_instReduceEvalNat___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalString___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalString___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalString = (const lean_object*)&l_Lean_Meta_instReduceEvalString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 63, 218, 129, 21, 133, 119, 116)}};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "anonymous"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 163, 3, 148, 15, 163, 84, 121)}};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalName___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalName___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalName = (const lean_object*)&l_Lean_Meta_instReduceEvalName___closed__0_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 240, 210, 97, 67, 170, 216, 80)}};
static const lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofFin"};
static const lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 167, 55, 152, 45, 146, 42, 51)}};
static const lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2 = (const lean_object*)&l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec(lean_object*);
static const lean_string_object l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_instReduceEvalBool___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_instReduceEvalBool___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_instReduceEvalBool___private__1___closed__2 = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_instReduceEvalBool___private__1___closed__3 = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_instReduceEvalBool___private__1___closed__4 = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalBool___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalBool___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalBool = (const lean_object*)&l_Lean_Meta_instReduceEvalBool___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "BinderInfo"};
static const lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2 = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "strictImplicit"};
static const lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3 = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3_value;
static const lean_string_object l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instImplicit"};
static const lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4 = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalBinderInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalBinderInfo = (const lean_object*)&l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Literal"};
static const lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 199, 201, 37, 137, 51, 1, 129)}};
static const lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2 = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value;
static const lean_string_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3 = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 249, 146, 84, 160, 212, 27)}};
static const lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4 = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalLiteral___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalLiteral___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalLiteral = (const lean_object*)&l_Lean_Meta_instReduceEvalLiteral___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "MVarId"};
static const lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 186, 234, 138, 172, 166, 87, 74)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 44, 60, 136, 72, 250, 230, 141)}};
static const lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalMVarId___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalMVarId = (const lean_object*)&l_Lean_Meta_instReduceEvalMVarId___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LevelMVarId"};
static const lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 60, 85, 89, 175, 240, 129, 147)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 157, 226, 48, 182, 72, 20, 234)}};
static const lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalLevelMVarId = (const lean_object*)&l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value;
static const lean_string_object l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "FVarId"};
static const lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 80, 170, 214, 218, 146, 55, 86)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 212, 153, 136, 172, 214, 179, 96)}};
static const lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalFVarId___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalFVarId = (const lean_object*)&l_Lean_Meta_instReduceEvalFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg(lean_object* v_inst_1_, lean_object* v_e_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
uint8_t v___y_9_; lean_object* v___x_24_; uint8_t v_transparency_25_; uint8_t v___x_26_; uint8_t v___x_27_; 
v___x_24_ = l_Lean_Meta_Context_config(v_a_3_);
v_transparency_25_ = lean_ctor_get_uint8(v___x_24_, 9);
lean_dec_ref(v___x_24_);
v___x_26_ = 1;
v___x_27_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_25_, v___x_26_);
if (v___x_27_ == 0)
{
v___y_9_ = v_transparency_25_;
goto v___jp_8_;
}
else
{
v___y_9_ = v___x_26_;
goto v___jp_8_;
}
v___jp_8_:
{
lean_object* v_keyedConfig_10_; uint8_t v_trackZetaDelta_11_; lean_object* v_zetaDeltaSet_12_; lean_object* v_lctx_13_; lean_object* v_localInstances_14_; lean_object* v_defEqCtx_x3f_15_; lean_object* v_synthPendingDepth_16_; lean_object* v_customCanUnfoldPredicate_x3f_17_; uint8_t v_univApprox_18_; uint8_t v_inTypeClassResolution_19_; uint8_t v_cacheInferType_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_keyedConfig_10_ = lean_ctor_get(v_a_3_, 0);
v_trackZetaDelta_11_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7);
v_zetaDeltaSet_12_ = lean_ctor_get(v_a_3_, 1);
v_lctx_13_ = lean_ctor_get(v_a_3_, 2);
v_localInstances_14_ = lean_ctor_get(v_a_3_, 3);
v_defEqCtx_x3f_15_ = lean_ctor_get(v_a_3_, 4);
v_synthPendingDepth_16_ = lean_ctor_get(v_a_3_, 5);
v_customCanUnfoldPredicate_x3f_17_ = lean_ctor_get(v_a_3_, 6);
v_univApprox_18_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_19_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 2);
v_cacheInferType_20_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_10_);
v___x_21_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_9_, v_keyedConfig_10_);
lean_inc(v_customCanUnfoldPredicate_x3f_17_);
lean_inc(v_synthPendingDepth_16_);
lean_inc(v_defEqCtx_x3f_15_);
lean_inc_ref(v_localInstances_14_);
lean_inc_ref(v_lctx_13_);
lean_inc(v_zetaDeltaSet_12_);
v___x_22_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_22_, 0, v___x_21_);
lean_ctor_set(v___x_22_, 1, v_zetaDeltaSet_12_);
lean_ctor_set(v___x_22_, 2, v_lctx_13_);
lean_ctor_set(v___x_22_, 3, v_localInstances_14_);
lean_ctor_set(v___x_22_, 4, v_defEqCtx_x3f_15_);
lean_ctor_set(v___x_22_, 5, v_synthPendingDepth_16_);
lean_ctor_set(v___x_22_, 6, v_customCanUnfoldPredicate_x3f_17_);
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*7, v_trackZetaDelta_11_);
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*7 + 1, v_univApprox_18_);
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*7 + 2, v_inTypeClassResolution_19_);
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*7 + 3, v_cacheInferType_20_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
v___x_23_ = lean_apply_6(v_inst_1_, v_e_2_, v___x_22_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object* v_inst_28_, lean_object* v_e_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_reduceEval___redArg(v_inst_28_, v_e_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_e_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_reduceEval___redArg(v_inst_37_, v_e_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_reduceEval(v_00_u03b1_45_, v_inst_46_, v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(lean_object* v_msgData_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_env_61_; lean_object* v___x_62_; lean_object* v_mctx_63_; lean_object* v_lctx_64_; lean_object* v_options_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_60_ = lean_st_ref_get(v___y_58_);
v_env_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_env_61_);
lean_dec(v___x_60_);
v___x_62_ = lean_st_ref_get(v___y_56_);
v_mctx_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_mctx_63_);
lean_dec(v___x_62_);
v_lctx_64_ = lean_ctor_get(v___y_55_, 2);
v_options_65_ = lean_ctor_get(v___y_57_, 2);
lean_inc_ref(v_options_65_);
lean_inc_ref(v_lctx_64_);
v___x_66_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_66_, 0, v_env_61_);
lean_ctor_set(v___x_66_, 1, v_mctx_63_);
lean_ctor_set(v___x_66_, 2, v_lctx_64_);
lean_ctor_set(v___x_66_, 3, v_options_65_);
v___x_67_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_msgData_54_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_ref_82_; lean_object* v___x_83_; lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_ref_82_ = lean_ctor_get(v___y_79_, 5);
v___x_83_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_inc(v_ref_82_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_ref_82_);
lean_ctor_set(v___x_88_, 1, v_a_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 1);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object* v_e_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1, &l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once, _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
v___x_110_ = l_Lean_indentExpr(v_e_103_);
v___x_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_111_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object* v_e_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* v_00_u03b1_120_, lean_object* v_e_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* v_00_u03b1_128_, lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(v_00_u03b1_128_, v_e_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_object* v_00_u03b1_136_, lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(lean_object* v_00_u03b1_144_, lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_144_, v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1(lean_object* v_e_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
lean_inc(v_a_156_);
lean_inc_ref(v_a_155_);
lean_inc(v_a_154_);
lean_inc_ref(v_a_153_);
v___x_158_ = lean_whnf(v_e_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_n(v_a_159_, 2);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = l_Lean_Meta_evalNat(v_a_159_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_170_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_170_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
if (lean_obj_tag(v_a_161_) == 1)
{
lean_object* v_val_165_; lean_object* v___x_167_; 
lean_dec(v_a_159_);
v_val_165_ = lean_ctor_get(v_a_161_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v_a_161_, 1);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v_val_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_val_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_169_; 
lean_del_object(v___x_163_);
lean_dec(v_a_161_);
v___x_169_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_159_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
return v___x_169_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_a_159_);
v_a_171_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_160_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_160_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_158_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_158_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1___boxed(lean_object* v_e_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object* v_e_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; 
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
lean_inc(v___y_196_);
lean_inc_ref(v___y_195_);
v___x_200_ = lean_whnf(v_e_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_202_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_n(v_a_201_, 2);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = l_Lean_Meta_evalNat(v_a_201_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_212_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_212_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
if (lean_obj_tag(v_a_203_) == 1)
{
lean_object* v_val_207_; lean_object* v___x_209_; 
lean_dec(v_a_201_);
v_val_207_ = lean_ctor_get(v_a_203_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_a_203_, 1);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_val_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_val_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
else
{
lean_object* v___x_211_; 
lean_del_object(v___x_205_);
lean_dec(v_a_203_);
v___x_211_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_201_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
return v___x_211_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_201_);
v_a_213_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_202_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_202_);
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
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_200_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_200_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0___boxed(lean_object* v_e_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Meta_instReduceEvalNat___lam__0(v_e_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg(lean_object* v_inst_247_, lean_object* v_e_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; 
lean_inc(v_a_252_);
lean_inc_ref(v_a_251_);
lean_inc(v_a_250_);
lean_inc_ref(v_a_249_);
v___x_254_ = lean_whnf(v_e_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_299_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_299_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_299_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_299_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
uint8_t v___y_260_; lean_object* v___x_281_; 
v___x_281_ = l_Lean_Expr_getAppFn(v_a_255_);
if (lean_obj_tag(v___x_281_) == 4)
{
lean_object* v_declName_282_; lean_object* v___x_283_; uint8_t v___y_285_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_declName_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_declName_282_);
lean_dec_ref_known(v___x_281_, 2);
v___x_283_ = l_Lean_Expr_getAppNumArgs(v_a_255_);
v___x_294_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_295_ = lean_name_eq(v_declName_282_, v___x_294_);
if (v___x_295_ == 0)
{
v___y_285_ = v___x_295_;
goto v___jp_284_;
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_nat_dec_eq(v___x_283_, v___x_296_);
v___y_285_ = v___x_297_;
goto v___jp_284_;
}
v___jp_284_:
{
if (v___y_285_ == 0)
{
lean_object* v___x_286_; uint8_t v___x_287_; 
lean_del_object(v___x_257_);
v___x_286_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_287_ = lean_name_eq(v_declName_282_, v___x_286_);
lean_dec(v_declName_282_);
if (v___x_287_ == 0)
{
lean_dec(v___x_283_);
v___y_260_ = v___x_287_;
goto v___jp_259_;
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_dec_eq(v___x_283_, v___x_288_);
lean_dec(v___x_283_);
v___y_260_ = v___x_289_;
goto v___jp_259_;
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_dec(v___x_283_);
lean_dec(v_declName_282_);
lean_dec(v_a_255_);
lean_dec_ref(v_inst_247_);
v___x_290_ = lean_box(0);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_290_);
v___x_292_ = v___x_257_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_298_; 
lean_dec_ref(v___x_281_);
lean_del_object(v___x_257_);
lean_dec_ref(v_inst_247_);
v___x_298_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_255_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
return v___x_298_;
}
v___jp_259_:
{
if (v___y_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v_inst_247_);
v___x_261_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_255_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = l_Lean_Expr_appArg_x21(v_a_255_);
lean_dec(v_a_255_);
v___x_263_ = l_Lean_Meta_reduceEval___redArg(v_inst_247_, v___x_262_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_a_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_263_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_inst_247_);
v_a_300_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_254_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_254_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(lean_object* v_inst_308_, lean_object* v_e_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_308_, v_e_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1(lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_e_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
v___x_324_ = lean_whnf(v_e_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_369_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_369_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_369_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_369_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___y_330_; lean_object* v___x_351_; 
v___x_351_ = l_Lean_Expr_getAppFn(v_a_325_);
if (lean_obj_tag(v___x_351_) == 4)
{
lean_object* v_declName_352_; lean_object* v___x_353_; uint8_t v___y_355_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_declName_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_declName_352_);
lean_dec_ref_known(v___x_351_, 2);
v___x_353_ = l_Lean_Expr_getAppNumArgs(v_a_325_);
v___x_364_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_365_ = lean_name_eq(v_declName_352_, v___x_364_);
if (v___x_365_ == 0)
{
v___y_355_ = v___x_365_;
goto v___jp_354_;
}
else
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_dec_eq(v___x_353_, v___x_366_);
v___y_355_ = v___x_367_;
goto v___jp_354_;
}
v___jp_354_:
{
if (v___y_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
lean_del_object(v___x_327_);
v___x_356_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_357_ = lean_name_eq(v_declName_352_, v___x_356_);
lean_dec(v_declName_352_);
if (v___x_357_ == 0)
{
lean_dec(v___x_353_);
v___y_330_ = v___x_357_;
goto v___jp_329_;
}
else
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_dec_eq(v___x_353_, v___x_358_);
lean_dec(v___x_353_);
v___y_330_ = v___x_359_;
goto v___jp_329_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec(v___x_353_);
lean_dec(v_declName_352_);
lean_dec(v_a_325_);
lean_dec_ref(v_inst_317_);
v___x_360_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_360_);
v___x_362_ = v___x_327_;
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
lean_object* v___x_368_; 
lean_dec_ref(v___x_351_);
lean_del_object(v___x_327_);
lean_dec_ref(v_inst_317_);
v___x_368_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_325_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
return v___x_368_;
}
v___jp_329_:
{
if (v___y_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_inst_317_);
v___x_331_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_325_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = l_Lean_Expr_appArg_x21(v_a_325_);
lean_dec(v_a_325_);
v___x_333_ = l_Lean_Meta_reduceEval___redArg(v_inst_317_, v___x_332_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_a_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_333_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_333_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_inst_317_);
v_a_370_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_324_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_324_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___boxed(lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_instReduceEvalOption___private__1(v_00_u03b1_378_, v_inst_379_, v_e_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object* v_inst_387_, lean_object* v_e_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
v___x_394_ = lean_whnf(v_e_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_439_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_439_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_439_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_439_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___y_400_; lean_object* v___x_421_; 
v___x_421_ = l_Lean_Expr_getAppFn(v_a_395_);
if (lean_obj_tag(v___x_421_) == 4)
{
lean_object* v_declName_422_; lean_object* v___x_423_; uint8_t v___y_425_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_declName_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_declName_422_);
lean_dec_ref_known(v___x_421_, 2);
v___x_423_ = l_Lean_Expr_getAppNumArgs(v_a_395_);
v___x_434_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_435_ = lean_name_eq(v_declName_422_, v___x_434_);
if (v___x_435_ == 0)
{
v___y_425_ = v___x_435_;
goto v___jp_424_;
}
else
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_dec_eq(v___x_423_, v___x_436_);
v___y_425_ = v___x_437_;
goto v___jp_424_;
}
v___jp_424_:
{
if (v___y_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
lean_del_object(v___x_397_);
v___x_426_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_427_ = lean_name_eq(v_declName_422_, v___x_426_);
lean_dec(v_declName_422_);
if (v___x_427_ == 0)
{
lean_dec(v___x_423_);
v___y_400_ = v___x_427_;
goto v___jp_399_;
}
else
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_dec_eq(v___x_423_, v___x_428_);
lean_dec(v___x_423_);
v___y_400_ = v___x_429_;
goto v___jp_399_;
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec(v___x_423_);
lean_dec(v_declName_422_);
lean_dec(v_a_395_);
lean_dec_ref(v_inst_387_);
v___x_430_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_430_);
v___x_432_ = v___x_397_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v___x_438_; 
lean_dec_ref(v___x_421_);
lean_del_object(v___x_397_);
lean_dec_ref(v_inst_387_);
v___x_438_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_395_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
return v___x_438_;
}
v___jp_399_:
{
if (v___y_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v_inst_387_);
v___x_401_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_395_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = l_Lean_Expr_appArg_x21(v_a_395_);
lean_dec(v_a_395_);
v___x_403_ = l_Lean_Meta_reduceEval___redArg(v_inst_387_, v___x_402_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_413_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_403_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_403_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_inst_387_);
v_a_440_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_394_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_394_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(lean_object* v_inst_448_, lean_object* v_e_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(v_inst_448_, v_e_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object* v_inst_456_){
_start:
{
lean_object* v___f_457_; 
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_457_, 0, v_inst_456_);
return v___f_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* v_00_u03b1_458_, lean_object* v_inst_459_){
_start:
{
lean_object* v___f_460_; 
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_460_, 0, v_inst_459_);
return v___f_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_467_; 
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
lean_inc(v_a_463_);
lean_inc_ref(v_a_462_);
lean_inc_ref(v_e_461_);
v___x_467_ = lean_whnf(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_479_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_479_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
if (lean_obj_tag(v_a_468_) == 9)
{
lean_object* v_a_472_; 
v_a_472_ = lean_ctor_get(v_a_468_, 0);
lean_inc_ref(v_a_472_);
lean_dec_ref_known(v_a_468_, 1);
if (lean_obj_tag(v_a_472_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_475_; 
lean_dec_ref(v_e_461_);
v_val_473_ = lean_ctor_get(v_a_472_, 0);
lean_inc_ref(v_val_473_);
lean_dec_ref_known(v_a_472_, 1);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v_val_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_val_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v___x_477_; 
lean_dec_ref(v_a_472_);
lean_del_object(v___x_470_);
v___x_477_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_477_;
}
}
else
{
lean_object* v___x_478_; 
lean_del_object(v___x_470_);
lean_dec(v_a_468_);
v___x_478_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_478_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_e_461_);
v_a_480_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_467_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_467_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1___boxed(lean_object* v_e_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object* v_e_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc_ref(v_e_495_);
v___x_501_ = lean_whnf(v_e_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_513_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_513_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_513_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_513_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
if (lean_obj_tag(v_a_502_) == 9)
{
lean_object* v_a_506_; 
v_a_506_ = lean_ctor_get(v_a_502_, 0);
lean_inc_ref(v_a_506_);
lean_dec_ref_known(v_a_502_, 1);
if (lean_obj_tag(v_a_506_) == 1)
{
lean_object* v_val_507_; lean_object* v___x_509_; 
lean_dec_ref(v_e_495_);
v_val_507_ = lean_ctor_get(v_a_506_, 0);
lean_inc_ref(v_val_507_);
lean_dec_ref_known(v_a_506_, 1);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v_val_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_val_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_a_506_);
lean_del_object(v___x_504_);
v___x_511_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; 
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
v___x_512_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_512_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_e_495_);
v_a_514_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_501_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_501_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0___boxed(lean_object* v_e_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_instReduceEvalString___lam__0(v_e_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object* v_e_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
uint8_t v___y_538_; lean_object* v___x_581_; uint8_t v_transparency_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_581_ = l_Lean_Meta_Context_config(v_a_532_);
v_transparency_582_ = lean_ctor_get_uint8(v___x_581_, 9);
lean_dec_ref(v___x_581_);
v___x_583_ = 1;
v___x_584_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_582_, v___x_583_);
if (v___x_584_ == 0)
{
v___y_538_ = v_transparency_582_;
goto v___jp_537_;
}
else
{
v___y_538_ = v___x_583_;
goto v___jp_537_;
}
v___jp_537_:
{
lean_object* v_keyedConfig_539_; uint8_t v_trackZetaDelta_540_; lean_object* v_zetaDeltaSet_541_; lean_object* v_lctx_542_; lean_object* v_localInstances_543_; lean_object* v_defEqCtx_x3f_544_; lean_object* v_synthPendingDepth_545_; lean_object* v_customCanUnfoldPredicate_x3f_546_; uint8_t v_univApprox_547_; uint8_t v_inTypeClassResolution_548_; uint8_t v_cacheInferType_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_keyedConfig_539_ = lean_ctor_get(v_a_532_, 0);
v_trackZetaDelta_540_ = lean_ctor_get_uint8(v_a_532_, sizeof(void*)*7);
v_zetaDeltaSet_541_ = lean_ctor_get(v_a_532_, 1);
v_lctx_542_ = lean_ctor_get(v_a_532_, 2);
v_localInstances_543_ = lean_ctor_get(v_a_532_, 3);
v_defEqCtx_x3f_544_ = lean_ctor_get(v_a_532_, 4);
v_synthPendingDepth_545_ = lean_ctor_get(v_a_532_, 5);
v_customCanUnfoldPredicate_x3f_546_ = lean_ctor_get(v_a_532_, 6);
v_univApprox_547_ = lean_ctor_get_uint8(v_a_532_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_548_ = lean_ctor_get_uint8(v_a_532_, sizeof(void*)*7 + 2);
v_cacheInferType_549_ = lean_ctor_get_uint8(v_a_532_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_539_);
v___x_550_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_538_, v_keyedConfig_539_);
lean_inc(v_customCanUnfoldPredicate_x3f_546_);
lean_inc(v_synthPendingDepth_545_);
lean_inc(v_defEqCtx_x3f_544_);
lean_inc_ref(v_localInstances_543_);
lean_inc_ref(v_lctx_542_);
lean_inc(v_zetaDeltaSet_541_);
v___x_551_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_zetaDeltaSet_541_);
lean_ctor_set(v___x_551_, 2, v_lctx_542_);
lean_ctor_set(v___x_551_, 3, v_localInstances_543_);
lean_ctor_set(v___x_551_, 4, v_defEqCtx_x3f_544_);
lean_ctor_set(v___x_551_, 5, v_synthPendingDepth_545_);
lean_ctor_set(v___x_551_, 6, v_customCanUnfoldPredicate_x3f_546_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*7, v_trackZetaDelta_540_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*7 + 1, v_univApprox_547_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*7 + 2, v_inTypeClassResolution_548_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*7 + 3, v_cacheInferType_549_);
lean_inc(v_a_535_);
lean_inc_ref(v_a_534_);
lean_inc(v_a_533_);
lean_inc_ref(v___x_551_);
v___x_552_ = lean_whnf(v_e_531_, v___x_551_, v_a_533_, v_a_534_, v_a_535_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_n(v_a_553_, 2);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = l_Lean_Meta_evalNat(v_a_553_, v___x_551_, v_a_533_, v_a_534_, v_a_535_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_564_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
if (lean_obj_tag(v_a_555_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_561_; 
lean_dec(v_a_553_);
lean_dec_ref_known(v___x_551_, 7);
v_val_559_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_a_555_, 1);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_val_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_val_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; 
lean_del_object(v___x_557_);
lean_dec(v_a_555_);
v___x_563_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_553_, v___x_551_, v_a_533_, v_a_534_, v_a_535_);
lean_dec_ref_known(v___x_551_, 7);
return v___x_563_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_a_553_);
lean_dec_ref_known(v___x_551_, 7);
v_a_565_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_554_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_554_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref_known(v___x_551_, 7);
v_a_573_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_552_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_552_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object* v_e_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object* v_e_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
uint8_t v___y_599_; lean_object* v___x_634_; uint8_t v_transparency_635_; uint8_t v___x_636_; uint8_t v___x_637_; 
v___x_634_ = l_Lean_Meta_Context_config(v_a_593_);
v_transparency_635_ = lean_ctor_get_uint8(v___x_634_, 9);
lean_dec_ref(v___x_634_);
v___x_636_ = 1;
v___x_637_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_635_, v___x_636_);
if (v___x_637_ == 0)
{
v___y_599_ = v_transparency_635_;
goto v___jp_598_;
}
else
{
v___y_599_ = v___x_636_;
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v_keyedConfig_600_; uint8_t v_trackZetaDelta_601_; lean_object* v_zetaDeltaSet_602_; lean_object* v_lctx_603_; lean_object* v_localInstances_604_; lean_object* v_defEqCtx_x3f_605_; lean_object* v_synthPendingDepth_606_; lean_object* v_customCanUnfoldPredicate_x3f_607_; uint8_t v_univApprox_608_; uint8_t v_inTypeClassResolution_609_; uint8_t v_cacheInferType_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_keyedConfig_600_ = lean_ctor_get(v_a_593_, 0);
v_trackZetaDelta_601_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*7);
v_zetaDeltaSet_602_ = lean_ctor_get(v_a_593_, 1);
v_lctx_603_ = lean_ctor_get(v_a_593_, 2);
v_localInstances_604_ = lean_ctor_get(v_a_593_, 3);
v_defEqCtx_x3f_605_ = lean_ctor_get(v_a_593_, 4);
v_synthPendingDepth_606_ = lean_ctor_get(v_a_593_, 5);
v_customCanUnfoldPredicate_x3f_607_ = lean_ctor_get(v_a_593_, 6);
v_univApprox_608_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_609_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*7 + 2);
v_cacheInferType_610_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_600_);
v___x_611_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_599_, v_keyedConfig_600_);
lean_inc(v_customCanUnfoldPredicate_x3f_607_);
lean_inc(v_synthPendingDepth_606_);
lean_inc(v_defEqCtx_x3f_605_);
lean_inc_ref(v_localInstances_604_);
lean_inc_ref(v_lctx_603_);
lean_inc(v_zetaDeltaSet_602_);
v___x_612_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_zetaDeltaSet_602_);
lean_ctor_set(v___x_612_, 2, v_lctx_603_);
lean_ctor_set(v___x_612_, 3, v_localInstances_604_);
lean_ctor_set(v___x_612_, 4, v_defEqCtx_x3f_605_);
lean_ctor_set(v___x_612_, 5, v_synthPendingDepth_606_);
lean_ctor_set(v___x_612_, 6, v_customCanUnfoldPredicate_x3f_607_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*7, v_trackZetaDelta_601_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*7 + 1, v_univApprox_608_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*7 + 2, v_inTypeClassResolution_609_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*7 + 3, v_cacheInferType_610_);
lean_inc(v_a_596_);
lean_inc_ref(v_a_595_);
lean_inc(v_a_594_);
lean_inc_ref(v___x_612_);
lean_inc_ref(v_e_592_);
v___x_613_ = lean_whnf(v_e_592_, v___x_612_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_625_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
if (lean_obj_tag(v_a_614_) == 9)
{
lean_object* v_a_618_; 
v_a_618_ = lean_ctor_get(v_a_614_, 0);
lean_inc_ref(v_a_618_);
lean_dec_ref_known(v_a_614_, 1);
if (lean_obj_tag(v_a_618_) == 1)
{
lean_object* v_val_619_; lean_object* v___x_621_; 
lean_dec_ref_known(v___x_612_, 7);
lean_dec_ref(v_e_592_);
v_val_619_ = lean_ctor_get(v_a_618_, 0);
lean_inc_ref(v_val_619_);
lean_dec_ref_known(v_a_618_, 1);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v_val_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec_ref(v_a_618_);
lean_del_object(v___x_616_);
v___x_623_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_592_, v___x_612_, v_a_594_, v_a_595_, v_a_596_);
lean_dec_ref_known(v___x_612_, 7);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; 
lean_del_object(v___x_616_);
lean_dec(v_a_614_);
v___x_624_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_592_, v___x_612_, v_a_594_, v_a_595_, v_a_596_);
lean_dec_ref_known(v___x_612_, 7);
return v___x_624_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref_known(v___x_612_, 7);
lean_dec_ref(v_e_592_);
v_a_626_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_613_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_613_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
return v_res_644_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object* v___x_645_, lean_object* v_00___646_){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_nat_dec_eq(v___x_645_, v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object* v___x_649_, lean_object* v_00___650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_649_, v_00___650_);
lean_dec(v___x_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
lean_inc(v_a_674_);
lean_inc_ref(v_a_673_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
v___x_676_ = lean_whnf(v_e_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_758_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_758_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_758_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_758_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Expr_getAppFn(v_a_677_);
if (lean_obj_tag(v___x_681_) == 4)
{
lean_object* v_declName_682_; lean_object* v___x_683_; uint8_t v___y_685_; uint8_t v___y_713_; uint8_t v___y_744_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_declName_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_declName_682_);
lean_dec_ref_known(v___x_681_, 2);
v___x_683_ = l_Lean_Expr_getAppNumArgs(v_a_677_);
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7));
v___x_754_ = lean_name_eq(v_declName_682_, v___x_753_);
if (v___x_754_ == 0)
{
v___y_744_ = v___x_754_;
goto v___jp_743_;
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_nat_dec_eq(v___x_683_, v___x_755_);
v___y_744_ = v___x_756_;
goto v___jp_743_;
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
lean_object* v___x_686_; 
lean_dec(v___x_683_);
v___x_686_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_677_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v___x_683_, v___x_687_);
lean_dec(v___x_683_);
lean_inc(v___x_688_);
v___x_689_ = l_Lean_Expr_getRevArg_x21(v_a_677_, v___x_688_);
v___x_690_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_689_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_nat_sub(v___x_688_, v___x_687_);
lean_dec(v___x_688_);
v___x_693_ = l_Lean_Expr_getRevArg_x21(v_a_677_, v___x_692_);
lean_dec(v_a_677_);
v___x_694_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_693_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = l_Lean_Name_num___override(v_a_691_, v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_a_691_);
v_a_704_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_694_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_694_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_dec(v___x_688_);
lean_dec(v_a_677_);
return v___x_690_;
}
}
}
v___jp_712_:
{
if (v___y_713_ == 0)
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3));
v___x_715_ = lean_name_eq(v_declName_682_, v___x_714_);
lean_dec(v_declName_682_);
if (v___x_715_ == 0)
{
v___y_685_ = v___x_715_;
goto v___jp_684_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_683_, v___x_716_);
v___y_685_ = v___x_717_;
goto v___jp_684_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_declName_682_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_sub(v___x_683_, v___x_718_);
lean_dec(v___x_683_);
lean_inc(v___x_719_);
v___x_720_ = l_Lean_Expr_getRevArg_x21(v_a_677_, v___x_719_);
v___x_721_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_720_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_nat_sub(v___x_719_, v___x_718_);
lean_dec(v___x_719_);
v___x_724_ = l_Lean_Expr_getRevArg_x21(v_a_677_, v___x_723_);
lean_dec(v_a_677_);
v___x_725_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_724_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = l_Lean_Name_str___override(v_a_722_, v_a_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_a_722_);
v_a_735_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_725_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_725_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_dec(v___x_719_);
lean_dec(v_a_677_);
return v___x_721_;
}
}
}
v___jp_743_:
{
if (v___y_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
lean_del_object(v___x_679_);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5));
v___x_746_ = lean_name_eq(v_declName_682_, v___x_745_);
if (v___x_746_ == 0)
{
v___y_713_ = v___x_746_;
goto v___jp_712_;
}
else
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = lean_box(0);
v___x_748_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_683_, v___x_747_);
v___y_713_ = v___x_748_;
goto v___jp_712_;
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec(v___x_683_);
lean_dec(v_declName_682_);
lean_dec(v_a_677_);
v___x_749_ = lean_box(0);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_749_);
v___x_751_ = v___x_679_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v___x_757_; 
lean_dec_ref(v___x_681_);
lean_del_object(v___x_679_);
v___x_757_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_677_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_757_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_676_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_676_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(lean_object* v_e_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1(lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1___boxed(lean_object* v_e_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_instReduceEvalName___private__1(v_e_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(lean_object* v_inst_793_, lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
lean_inc(v_a_798_);
lean_inc_ref(v_a_797_);
lean_inc(v_a_796_);
lean_inc_ref(v_a_795_);
v___x_800_ = lean_whnf(v_e_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_862_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_862_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_862_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_862_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Expr_getAppFn(v_a_801_);
if (lean_obj_tag(v___x_805_) == 4)
{
lean_object* v_declName_806_; 
v_declName_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_declName_806_);
lean_dec_ref_known(v___x_805_, 2);
if (lean_obj_tag(v_declName_806_) == 1)
{
lean_object* v_pre_807_; 
v_pre_807_ = lean_ctor_get(v_declName_806_, 0);
lean_inc(v_pre_807_);
if (lean_obj_tag(v_pre_807_) == 1)
{
lean_object* v_pre_808_; 
v_pre_808_ = lean_ctor_get(v_pre_807_, 0);
if (lean_obj_tag(v_pre_808_) == 0)
{
lean_object* v_str_809_; lean_object* v_str_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_str_809_ = lean_ctor_get(v_declName_806_, 1);
lean_inc_ref(v_str_809_);
lean_dec_ref_known(v_declName_806_, 2);
v_str_810_ = lean_ctor_get(v_pre_807_, 1);
lean_inc_ref(v_str_810_);
lean_dec_ref_known(v_pre_807_, 2);
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0));
v___x_812_ = lean_string_dec_eq(v_str_810_, v___x_811_);
lean_dec_ref(v_str_810_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec_ref(v_str_809_);
lean_del_object(v___x_803_);
lean_dec_ref(v_inst_793_);
v___x_813_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_814_ = l_Lean_Expr_getAppNumArgs(v_a_801_);
v___x_815_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1));
v___x_816_ = lean_string_dec_eq(v_str_809_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; uint8_t v___x_818_; 
lean_del_object(v___x_803_);
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2));
v___x_818_ = lean_string_dec_eq(v_str_809_, v___x_817_);
lean_dec_ref(v_str_809_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v___x_814_);
lean_dec_ref(v_inst_793_);
v___x_819_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(3u);
v___x_821_ = lean_nat_dec_eq(v___x_814_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_dec(v___x_814_);
lean_dec_ref(v_inst_793_);
v___x_822_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_sub(v___x_814_, v___x_823_);
v___x_825_ = lean_nat_sub(v___x_824_, v___x_823_);
lean_dec(v___x_824_);
v___x_826_ = l_Lean_Expr_getRevArg_x21(v_a_801_, v___x_825_);
lean_inc_ref(v_inst_793_);
v___x_827_ = l_Lean_Meta_reduceEval___redArg(v_inst_793_, v___x_826_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___x_829_ = lean_unsigned_to_nat(2u);
v___x_830_ = lean_nat_sub(v___x_814_, v___x_829_);
lean_dec(v___x_814_);
v___x_831_ = lean_nat_sub(v___x_830_, v___x_823_);
lean_dec(v___x_830_);
v___x_832_ = l_Lean_Expr_getRevArg_x21(v_a_801_, v___x_831_);
lean_dec(v_a_801_);
v___x_833_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_793_, v___x_832_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v_a_828_);
lean_ctor_set(v___x_838_, 1, v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_dec(v_a_828_);
return v___x_833_;
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v___x_814_);
lean_dec(v_a_801_);
lean_dec_ref(v_inst_793_);
v_a_843_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_827_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_827_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
else
{
lean_object* v___x_851_; uint8_t v___x_852_; 
lean_dec_ref(v_str_809_);
lean_dec_ref(v_inst_793_);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_dec_eq(v___x_814_, v___x_851_);
lean_dec(v___x_814_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_del_object(v___x_803_);
v___x_853_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_a_801_);
v___x_854_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_854_);
v___x_856_ = v___x_803_;
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
}
else
{
lean_object* v___x_858_; 
lean_dec_ref_known(v_pre_807_, 2);
lean_dec_ref_known(v_declName_806_, 2);
lean_del_object(v___x_803_);
lean_dec_ref(v_inst_793_);
v___x_858_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_858_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec_ref_known(v_declName_806_, 2);
lean_dec(v_pre_807_);
lean_del_object(v___x_803_);
lean_dec_ref(v_inst_793_);
v___x_859_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_859_;
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v_declName_806_);
lean_del_object(v___x_803_);
lean_dec_ref(v_inst_793_);
v___x_860_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_860_;
}
}
else
{
lean_object* v___x_861_; 
lean_dec_ref(v___x_805_);
lean_del_object(v___x_803_);
lean_dec_ref(v_inst_793_);
v___x_861_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_801_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_861_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v_inst_793_);
v_a_863_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_800_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_800_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(lean_object* v_inst_871_, lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_871_, v_e_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_object* v_00_u03b1_879_, lean_object* v_inst_880_, lean_object* v_e_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_880_, v_e_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(lean_object* v_00_u03b1_888_, lean_object* v_inst_889_, lean_object* v_e_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(v_00_u03b1_888_, v_inst_889_, v_e_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg(lean_object* v_inst_897_, lean_object* v_e_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_897_, v_e_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(lean_object* v_inst_905_, lean_object* v_e_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(v_inst_905_, v_e_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1(lean_object* v_00_u03b1_913_, lean_object* v_inst_914_, lean_object* v_e_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_914_, v_e_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___boxed(lean_object* v_00_u03b1_922_, lean_object* v_inst_923_, lean_object* v_e_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Meta_instReduceEvalList___private__1(v_00_u03b1_922_, v_inst_923_, v_e_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___redArg(lean_object* v_inst_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_932_, 0, lean_box(0));
lean_closure_set(v___x_932_, 1, v_inst_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList(lean_object* v_00_u03b1_933_, lean_object* v_inst_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_935_, 0, lean_box(0));
lean_closure_set(v___x_935_, 1, v_inst_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(lean_object* v_n_941_, lean_object* v_e_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
lean_inc(v_a_946_);
lean_inc_ref(v_a_945_);
lean_inc(v_a_944_);
lean_inc_ref(v_a_943_);
v___x_948_ = lean_whnf(v_e_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_951_ = lean_unsigned_to_nat(3u);
v___x_952_ = l_Lean_Expr_isAppOfArity(v_a_949_, v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_949_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_953_;
}
else
{
lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___f_954_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = l_Lean_Expr_getAppNumArgs(v_a_949_);
v___x_957_ = lean_nat_sub(v___x_956_, v___x_955_);
lean_dec(v___x_956_);
v___x_958_ = lean_nat_sub(v___x_957_, v___x_955_);
lean_dec(v___x_957_);
v___x_959_ = l_Lean_Expr_getRevArg_x21(v_a_949_, v___x_958_);
lean_dec(v_a_949_);
v___x_960_ = l_Lean_Meta_reduceEval___redArg(v___f_954_, v___x_959_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_nat_mod(v_a_961_, v_n_941_);
lean_dec(v_a_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_960_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_960_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_948_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_948_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(lean_object* v_n_986_, lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_986_, v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_n_986_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(lean_object* v_n_994_, lean_object* v_inst_995_, lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; 
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
v___x_1002_ = lean_whnf(v_e_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1005_ = lean_unsigned_to_nat(3u);
v___x_1006_ = l_Lean_Expr_isAppOfArity(v_a_1003_, v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1003_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1007_;
}
else
{
lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___f_1008_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = l_Lean_Expr_getAppNumArgs(v_a_1003_);
v___x_1011_ = lean_nat_sub(v___x_1010_, v___x_1009_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_nat_sub(v___x_1011_, v___x_1009_);
lean_dec(v___x_1011_);
v___x_1013_ = l_Lean_Expr_getRevArg_x21(v_a_1003_, v___x_1012_);
lean_dec(v_a_1003_);
v___x_1014_ = l_Lean_Meta_reduceEval___redArg(v___f_1008_, v___x_1013_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = lean_nat_mod(v_a_1015_, v_n_994_);
lean_dec(v_a_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1014_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1014_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1002_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1002_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(lean_object* v_n_1040_, lean_object* v_inst_1041_, lean_object* v_e_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(v_n_1040_, v_inst_1041_, v_e_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_n_1040_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(lean_object* v_n_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1050_, 0, v_n_1049_);
lean_closure_set(v___x_1050_, 1, lean_box(0));
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat(lean_object* v_n_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1053_, 0, v_n_1051_);
lean_closure_set(v___x_1053_, 1, lean_box(0));
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1(lean_object* v_n_1059_, lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; 
lean_inc(v_a_1064_);
lean_inc_ref(v_a_1063_);
lean_inc(v_a_1062_);
lean_inc_ref(v_a_1061_);
v___x_1066_ = lean_whnf(v_e_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2));
v___x_1069_ = lean_unsigned_to_nat(2u);
v___x_1070_ = l_Lean_Expr_isAppOfArity(v_a_1067_, v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1067_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1072_ = lean_nat_pow(v___x_1069_, v_n_1059_);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_nat_sub(v___x_1072_, v___x_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_nat_add(v___x_1074_, v___x_1073_);
lean_dec(v___x_1074_);
v___x_1076_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1076_, 0, v___x_1075_);
lean_closure_set(v___x_1076_, 1, lean_box(0));
v___x_1077_ = l_Lean_Expr_getAppNumArgs(v_a_1067_);
v___x_1078_ = lean_nat_sub(v___x_1077_, v___x_1073_);
lean_dec(v___x_1077_);
v___x_1079_ = lean_nat_sub(v___x_1078_, v___x_1073_);
lean_dec(v___x_1078_);
v___x_1080_ = l_Lean_Expr_getRevArg_x21(v_a_1067_, v___x_1079_);
lean_dec(v_a_1067_);
v___x_1081_ = l_Lean_Meta_reduceEval___redArg(v___x_1076_, v___x_1080_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1081_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1081_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1066_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1066_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(lean_object* v_n_1106_, lean_object* v_e_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Meta_instReduceEvalBitVec___private__1(v_n_1106_, v_e_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_n_1106_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec(lean_object* v_n_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalBitVec___private__1___boxed), 7, 1);
lean_closure_set(v___x_1115_, 0, v_n_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1(lean_object* v_e_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
lean_inc(v_a_1129_);
lean_inc_ref(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc_ref(v_a_1126_);
v___x_1131_ = lean_whnf(v_e_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1149_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1149_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1149_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__2));
v___x_1137_ = l_Lean_Expr_isAppOf(v_a_1132_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__4));
v___x_1139_ = l_Lean_Expr_isAppOf(v_a_1132_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_del_object(v___x_1134_);
v___x_1140_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1132_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_a_1132_);
v___x_1141_ = lean_box(v___x_1137_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1141_);
v___x_1143_ = v___x_1134_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_a_1132_);
v___x_1145_ = lean_box(v___x_1137_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1145_);
v___x_1147_ = v___x_1134_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1131_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1131_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1___boxed(lean_object* v_e_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_instReduceEvalBool___private__1(v_e_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1(lean_object* v_e_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
lean_inc(v_a_1176_);
lean_inc_ref(v_a_1175_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc_ref(v_e_1172_);
v___x_1178_ = lean_whnf(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1231_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1231_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1231_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Expr_constName_x3f(v_a_1179_);
lean_dec(v_a_1179_);
if (lean_obj_tag(v___x_1183_) == 1)
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v___x_1183_, 1);
if (lean_obj_tag(v_val_1184_) == 1)
{
lean_object* v_pre_1185_; 
v_pre_1185_ = lean_ctor_get(v_val_1184_, 0);
lean_inc(v_pre_1185_);
if (lean_obj_tag(v_pre_1185_) == 1)
{
lean_object* v_pre_1186_; 
v_pre_1186_ = lean_ctor_get(v_pre_1185_, 0);
lean_inc(v_pre_1186_);
if (lean_obj_tag(v_pre_1186_) == 1)
{
lean_object* v_pre_1187_; 
v_pre_1187_ = lean_ctor_get(v_pre_1186_, 0);
if (lean_obj_tag(v_pre_1187_) == 0)
{
lean_object* v_str_1188_; lean_object* v_str_1189_; lean_object* v_str_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_str_1188_ = lean_ctor_get(v_val_1184_, 1);
lean_inc_ref(v_str_1188_);
lean_dec_ref_known(v_val_1184_, 2);
v_str_1189_ = lean_ctor_get(v_pre_1185_, 1);
lean_inc_ref(v_str_1189_);
lean_dec_ref_known(v_pre_1185_, 2);
v_str_1190_ = lean_ctor_get(v_pre_1186_, 1);
lean_inc_ref(v_str_1190_);
lean_dec_ref_known(v_pre_1186_, 2);
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0));
v___x_1192_ = lean_string_dec_eq(v_str_1190_, v___x_1191_);
lean_dec_ref(v_str_1190_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_dec_ref(v_str_1189_);
lean_dec_ref(v_str_1188_);
lean_del_object(v___x_1181_);
v___x_1193_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0));
v___x_1195_ = lean_string_dec_eq(v_str_1189_, v___x_1194_);
lean_dec_ref(v_str_1189_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
lean_dec_ref(v_str_1188_);
lean_del_object(v___x_1181_);
v___x_1196_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1));
v___x_1198_ = lean_string_dec_eq(v_str_1188_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2));
v___x_1200_ = lean_string_dec_eq(v_str_1188_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3));
v___x_1202_ = lean_string_dec_eq(v_str_1188_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4));
v___x_1204_ = lean_string_dec_eq(v_str_1188_, v___x_1203_);
lean_dec_ref(v_str_1188_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_del_object(v___x_1181_);
v___x_1205_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1205_;
}
else
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_dec_ref(v_e_1172_);
v___x_1206_ = 3;
v___x_1207_ = lean_box(v___x_1206_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1207_);
v___x_1209_ = v___x_1181_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_dec_ref(v_str_1188_);
lean_dec_ref(v_e_1172_);
v___x_1211_ = 2;
v___x_1212_ = lean_box(v___x_1211_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1212_);
v___x_1214_ = v___x_1181_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
lean_dec_ref(v_str_1188_);
lean_dec_ref(v_e_1172_);
v___x_1216_ = 1;
v___x_1217_ = lean_box(v___x_1216_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1217_);
v___x_1219_ = v___x_1181_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec_ref(v_str_1188_);
lean_dec_ref(v_e_1172_);
v___x_1221_ = 0;
v___x_1222_ = lean_box(v___x_1221_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1222_);
v___x_1224_ = v___x_1181_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v___x_1226_; 
lean_dec_ref_known(v_pre_1186_, 2);
lean_dec_ref_known(v_pre_1185_, 2);
lean_dec_ref_known(v_val_1184_, 2);
lean_del_object(v___x_1181_);
v___x_1226_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1226_;
}
}
else
{
lean_object* v___x_1227_; 
lean_dec_ref_known(v_pre_1185_, 2);
lean_dec(v_pre_1186_);
lean_dec_ref_known(v_val_1184_, 2);
lean_del_object(v___x_1181_);
v___x_1227_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1227_;
}
}
else
{
lean_object* v___x_1228_; 
lean_dec_ref_known(v_val_1184_, 2);
lean_dec(v_pre_1185_);
lean_del_object(v___x_1181_);
v___x_1228_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1229_; 
lean_dec(v_val_1184_);
lean_del_object(v___x_1181_);
v___x_1229_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1229_;
}
}
else
{
lean_object* v___x_1230_; 
lean_dec(v___x_1183_);
lean_del_object(v___x_1181_);
v___x_1230_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1230_;
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_e_1172_);
v_a_1232_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1178_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1178_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(lean_object* v_e_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(v_e_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1(lean_object* v_e_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; 
lean_inc(v_a_1264_);
lean_inc_ref(v_a_1263_);
lean_inc(v_a_1262_);
lean_inc_ref(v_a_1261_);
v___x_1266_ = lean_whnf(v_e_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2));
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = l_Lean_Expr_isAppOfArity(v_a_1267_, v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4));
v___x_1272_ = l_Lean_Expr_isAppOfArity(v_a_1267_, v___x_1271_, v___x_1269_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
v___x_1273_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1267_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1273_;
}
else
{
lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___f_1274_ = ((lean_object*)(l_Lean_Meta_instReduceEvalString___closed__0));
v___x_1275_ = l_Lean_Expr_getAppNumArgs(v_a_1267_);
v___x_1276_ = lean_nat_sub(v___x_1275_, v___x_1269_);
lean_dec(v___x_1275_);
v___x_1277_ = l_Lean_Expr_getRevArg_x21(v_a_1267_, v___x_1276_);
lean_dec(v_a_1267_);
v___x_1278_ = l_Lean_Meta_reduceEval___redArg(v___f_1274_, v___x_1277_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_a_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1278_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1278_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___f_1296_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1297_ = l_Lean_Expr_getAppNumArgs(v_a_1267_);
v___x_1298_ = lean_nat_sub(v___x_1297_, v___x_1269_);
lean_dec(v___x_1297_);
v___x_1299_ = l_Lean_Expr_getRevArg_x21(v_a_1267_, v___x_1298_);
lean_dec(v_a_1267_);
v___x_1300_ = l_Lean_Meta_reduceEval___redArg(v___f_1296_, v___x_1299_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_a_1301_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1300_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1300_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1266_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1266_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(lean_object* v_e_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_instReduceEvalLiteral___private__1(v_e_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; 
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
v___x_1346_ = lean_whnf(v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = l_Lean_Expr_isAppOfArity(v_a_1347_, v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1347_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1352_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1353_ = l_Lean_Expr_getAppNumArgs(v_a_1347_);
v___x_1354_ = lean_nat_sub(v___x_1353_, v___x_1349_);
lean_dec(v___x_1353_);
v___x_1355_ = l_Lean_Expr_getRevArg_x21(v_a_1347_, v___x_1354_);
lean_dec(v_a_1347_);
v___x_1356_ = l_Lean_Meta_reduceEval___redArg(v___x_1352_, v___x_1355_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1356_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1356_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1346_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1346_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object* v_e_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_instReduceEvalMVarId___private__1(v_e_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0(lean_object* v_e_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
v___x_1394_ = lean_whnf(v_e_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = l_Lean_Expr_isAppOfArity(v_a_1395_, v___x_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1395_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1400_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1401_ = l_Lean_Expr_getAppNumArgs(v_a_1395_);
v___x_1402_ = lean_nat_sub(v___x_1401_, v___x_1397_);
lean_dec(v___x_1401_);
v___x_1403_ = l_Lean_Expr_getRevArg_x21(v_a_1395_, v___x_1402_);
lean_dec(v_a_1395_);
v___x_1404_ = l_Lean_Meta_reduceEval___redArg(v___x_1400_, v___x_1403_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1404_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1404_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1421_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1394_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1394_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed(lean_object* v_e_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(v_e_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1(lean_object* v_e_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; 
lean_inc(v_a_1447_);
lean_inc_ref(v_a_1446_);
lean_inc(v_a_1445_);
lean_inc_ref(v_a_1444_);
v___x_1449_ = lean_whnf(v_e_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = l_Lean_Expr_isAppOfArity(v_a_1450_, v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1450_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1455_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1456_ = l_Lean_Expr_getAppNumArgs(v_a_1450_);
v___x_1457_ = lean_nat_sub(v___x_1456_, v___x_1452_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_Expr_getRevArg_x21(v_a_1450_, v___x_1457_);
lean_dec(v_a_1450_);
v___x_1459_ = l_Lean_Meta_reduceEval___redArg(v___x_1455_, v___x_1458_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1459_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1459_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1449_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1449_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(lean_object* v_e_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(v_e_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(lean_object* v_e_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; 
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
v___x_1497_ = lean_whnf(v_e_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = l_Lean_Expr_isAppOfArity(v_a_1498_, v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1498_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1503_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1504_ = l_Lean_Expr_getAppNumArgs(v_a_1498_);
v___x_1505_ = lean_nat_sub(v___x_1504_, v___x_1500_);
lean_dec(v___x_1504_);
v___x_1506_ = l_Lean_Expr_getRevArg_x21(v_a_1498_, v___x_1505_);
lean_dec(v_a_1498_);
v___x_1507_ = l_Lean_Meta_reduceEval___redArg(v___x_1503_, v___x_1506_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_a_1516_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1507_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1507_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_a_1524_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1497_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1497_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed(lean_object* v_e_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(v_e_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1(lean_object* v_e_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; 
lean_inc(v_a_1550_);
lean_inc_ref(v_a_1549_);
lean_inc(v_a_1548_);
lean_inc_ref(v_a_1547_);
v___x_1552_ = lean_whnf(v_e_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = l_Lean_Expr_isAppOfArity(v_a_1553_, v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1553_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1558_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1559_ = l_Lean_Expr_getAppNumArgs(v_a_1553_);
v___x_1560_ = lean_nat_sub(v___x_1559_, v___x_1555_);
lean_dec(v___x_1559_);
v___x_1561_ = l_Lean_Expr_getRevArg_x21(v_a_1553_, v___x_1560_);
lean_dec(v_a_1553_);
v___x_1562_ = l_Lean_Meta_reduceEval___redArg(v___x_1558_, v___x_1561_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_a_1571_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1562_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1562_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_a_1579_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1552_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1552_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(lean_object* v_e_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_instReduceEvalFVarId___private__1(v_e_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0(lean_object* v_e_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
v___x_1600_ = lean_whnf(v_e_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = l_Lean_Expr_isAppOfArity(v_a_1601_, v___x_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1601_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1606_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1607_ = l_Lean_Expr_getAppNumArgs(v_a_1601_);
v___x_1608_ = lean_nat_sub(v___x_1607_, v___x_1603_);
lean_dec(v___x_1607_);
v___x_1609_ = l_Lean_Expr_getRevArg_x21(v_a_1601_, v___x_1608_);
lean_dec(v_a_1601_);
v___x_1610_ = l_Lean_Meta_reduceEval___redArg(v___x_1606_, v___x_1609_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1610_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1610_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1600_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1600_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed(lean_object* v_e_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(v_e_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1641_;
}
}
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ReduceEval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ReduceEval(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ReduceEval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ReduceEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ReduceEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ReduceEval(builtin);
}
#ifdef __cplusplus
}
#endif
