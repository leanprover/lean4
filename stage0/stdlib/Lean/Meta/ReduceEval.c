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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* v___y_9_; lean_object* v___x_26_; uint8_t v_transparency_27_; uint8_t v___x_28_; uint8_t v___x_29_; 
v___x_26_ = l_Lean_Meta_Context_config(v_a_3_);
v_transparency_27_ = lean_ctor_get_uint8(v___x_26_, 9);
lean_dec_ref(v___x_26_);
v___x_28_ = 1;
v___x_29_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_27_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_30_ = lean_apply_6(v_inst_1_, v_e_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
v___y_9_ = v___x_30_;
goto v___jp_8_;
}
else
{
lean_object* v_keyedConfig_31_; uint8_t v_trackZetaDelta_32_; lean_object* v_zetaDeltaSet_33_; lean_object* v_lctx_34_; lean_object* v_localInstances_35_; lean_object* v_defEqCtx_x3f_36_; lean_object* v_synthPendingDepth_37_; lean_object* v_customCanUnfoldPredicate_x3f_38_; uint8_t v_univApprox_39_; uint8_t v_inTypeClassResolution_40_; uint8_t v_cacheInferType_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_keyedConfig_31_ = lean_ctor_get(v_a_3_, 0);
v_trackZetaDelta_32_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7);
v_zetaDeltaSet_33_ = lean_ctor_get(v_a_3_, 1);
v_lctx_34_ = lean_ctor_get(v_a_3_, 2);
v_localInstances_35_ = lean_ctor_get(v_a_3_, 3);
v_defEqCtx_x3f_36_ = lean_ctor_get(v_a_3_, 4);
v_synthPendingDepth_37_ = lean_ctor_get(v_a_3_, 5);
v_customCanUnfoldPredicate_x3f_38_ = lean_ctor_get(v_a_3_, 6);
v_univApprox_39_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_40_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 2);
v_cacheInferType_41_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_31_);
v___x_42_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_28_, v_keyedConfig_31_);
lean_inc(v_customCanUnfoldPredicate_x3f_38_);
lean_inc(v_synthPendingDepth_37_);
lean_inc(v_defEqCtx_x3f_36_);
lean_inc_ref(v_localInstances_35_);
lean_inc_ref(v_lctx_34_);
lean_inc(v_zetaDeltaSet_33_);
v___x_43_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v_zetaDeltaSet_33_);
lean_ctor_set(v___x_43_, 2, v_lctx_34_);
lean_ctor_set(v___x_43_, 3, v_localInstances_35_);
lean_ctor_set(v___x_43_, 4, v_defEqCtx_x3f_36_);
lean_ctor_set(v___x_43_, 5, v_synthPendingDepth_37_);
lean_ctor_set(v___x_43_, 6, v_customCanUnfoldPredicate_x3f_38_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*7, v_trackZetaDelta_32_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*7 + 1, v_univApprox_39_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*7 + 2, v_inTypeClassResolution_40_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*7 + 3, v_cacheInferType_41_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
v___x_44_ = lean_apply_6(v_inst_1_, v_e_2_, v___x_43_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
v___y_9_ = v___x_44_;
goto v___jp_8_;
}
v___jp_8_:
{
if (lean_obj_tag(v___y_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_17_; 
v_a_10_ = lean_ctor_get(v___y_9_, 0);
v_isSharedCheck_17_ = !lean_is_exclusive(v___y_9_);
if (v_isSharedCheck_17_ == 0)
{
v___x_12_ = v___y_9_;
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___y_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_a_10_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
v_a_18_ = lean_ctor_get(v___y_9_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___y_9_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___y_9_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___y_9_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object* v_inst_45_, lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_reduceEval___redArg(v_inst_45_, v_e_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_e_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Meta_reduceEval___redArg(v_inst_54_, v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_e_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_reduceEval(v_00_u03b1_62_, v_inst_63_, v_e_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(lean_object* v_msgData_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; lean_object* v_env_78_; lean_object* v___x_79_; lean_object* v_mctx_80_; lean_object* v_lctx_81_; lean_object* v_options_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_77_ = lean_st_ref_get(v___y_75_);
v_env_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_env_78_);
lean_dec(v___x_77_);
v___x_79_ = lean_st_ref_get(v___y_73_);
v_mctx_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_mctx_80_);
lean_dec(v___x_79_);
v_lctx_81_ = lean_ctor_get(v___y_72_, 2);
v_options_82_ = lean_ctor_get(v___y_74_, 1);
lean_inc_ref(v_options_82_);
lean_inc_ref(v_lctx_81_);
v___x_83_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_83_, 0, v_env_78_);
lean_ctor_set(v___x_83_, 1, v_mctx_80_);
lean_ctor_set(v___x_83_, 2, v_lctx_81_);
lean_ctor_set(v___x_83_, 3, v_options_82_);
v___x_84_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_msgData_71_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(lean_object* v_msgData_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_ref_99_; lean_object* v___x_100_; lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_ref_99_ = lean_ctor_get(v___y_96_, 4);
v___x_100_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
lean_inc(v_ref_99_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_ref_99_);
lean_ctor_set(v___x_105_, 1, v_a_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 1);
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0));
v___x_119_ = l_Lean_stringToMessageData(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object* v_e_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1, &l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once, _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
v___x_127_ = l_Lean_indentExpr(v_e_120_);
v___x_128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_128_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object* v_e_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* v_00_u03b1_137_, lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* v_00_u03b1_145_, lean_object* v_e_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(v_00_u03b1_145_, v_e_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_object* v_00_u03b1_153_, lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(lean_object* v_00_u03b1_161_, lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_161_, v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_175_; 
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
v___x_175_ = lean_whnf(v_e_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc_n(v_a_176_, 2);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = l_Lean_Meta_evalNat(v_a_176_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_187_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
if (lean_obj_tag(v_a_178_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_184_; 
lean_dec(v_a_176_);
v_val_182_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_a_178_, 1);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v_val_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_val_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v___x_186_; 
lean_del_object(v___x_180_);
lean_dec(v_a_178_);
v___x_186_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_176_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
return v___x_186_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_a_176_);
v_a_188_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_177_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_177_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_175_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_175_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1___boxed(lean_object* v_e_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object* v_e_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; 
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
v___x_217_ = lean_whnf(v_e_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_n(v_a_218_, 2);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = l_Lean_Meta_evalNat(v_a_218_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_229_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_229_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
if (lean_obj_tag(v_a_220_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_226_; 
lean_dec(v_a_218_);
v_val_224_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v_a_220_, 1);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v_val_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_val_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
else
{
lean_object* v___x_228_; 
lean_del_object(v___x_222_);
lean_dec(v_a_220_);
v___x_228_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_218_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
return v___x_228_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec(v_a_218_);
v_a_230_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_219_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_219_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_217_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_217_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0___boxed(lean_object* v_e_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_instReduceEvalNat___lam__0(v_e_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg(lean_object* v_inst_264_, lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
lean_inc(v_a_269_);
lean_inc_ref(v_a_268_);
lean_inc(v_a_267_);
lean_inc_ref(v_a_266_);
v___x_271_ = lean_whnf(v_e_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_316_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_316_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_316_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_316_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
uint8_t v___y_277_; lean_object* v___x_298_; 
v___x_298_ = l_Lean_Expr_getAppFn(v_a_272_);
if (lean_obj_tag(v___x_298_) == 4)
{
lean_object* v_declName_299_; lean_object* v___x_300_; uint8_t v___y_302_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_declName_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_declName_299_);
lean_dec_ref_known(v___x_298_, 2);
v___x_300_ = l_Lean_Expr_getAppNumArgs(v_a_272_);
v___x_311_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_312_ = lean_name_eq(v_declName_299_, v___x_311_);
if (v___x_312_ == 0)
{
v___y_302_ = v___x_312_;
goto v___jp_301_;
}
else
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_nat_dec_eq(v___x_300_, v___x_313_);
v___y_302_ = v___x_314_;
goto v___jp_301_;
}
v___jp_301_:
{
if (v___y_302_ == 0)
{
lean_object* v___x_303_; uint8_t v___x_304_; 
lean_del_object(v___x_274_);
v___x_303_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_304_ = lean_name_eq(v_declName_299_, v___x_303_);
lean_dec(v_declName_299_);
if (v___x_304_ == 0)
{
lean_dec(v___x_300_);
v___y_277_ = v___x_304_;
goto v___jp_276_;
}
else
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_dec_eq(v___x_300_, v___x_305_);
lean_dec(v___x_300_);
v___y_277_ = v___x_306_;
goto v___jp_276_;
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v___x_300_);
lean_dec(v_declName_299_);
lean_dec(v_a_272_);
lean_dec_ref(v_inst_264_);
v___x_307_ = lean_box(0);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_307_);
v___x_309_ = v___x_274_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v___x_315_; 
lean_dec_ref(v___x_298_);
lean_del_object(v___x_274_);
lean_dec_ref(v_inst_264_);
v___x_315_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_272_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_315_;
}
v___jp_276_:
{
if (v___y_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref(v_inst_264_);
v___x_278_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_272_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = l_Lean_Expr_appArg_x21(v_a_272_);
lean_dec(v_a_272_);
v___x_280_ = l_Lean_Meta_reduceEval___redArg(v_inst_264_, v___x_279_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
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
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_280_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_280_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_inst_264_);
v_a_317_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_271_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_271_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(lean_object* v_inst_325_, lean_object* v_e_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_325_, v_e_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, lean_object* v_e_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; 
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
v___x_341_ = lean_whnf(v_e_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_386_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_386_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_386_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_386_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
uint8_t v___y_347_; lean_object* v___x_368_; 
v___x_368_ = l_Lean_Expr_getAppFn(v_a_342_);
if (lean_obj_tag(v___x_368_) == 4)
{
lean_object* v_declName_369_; lean_object* v___x_370_; uint8_t v___y_372_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_declName_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_declName_369_);
lean_dec_ref_known(v___x_368_, 2);
v___x_370_ = l_Lean_Expr_getAppNumArgs(v_a_342_);
v___x_381_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_382_ = lean_name_eq(v_declName_369_, v___x_381_);
if (v___x_382_ == 0)
{
v___y_372_ = v___x_382_;
goto v___jp_371_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_nat_dec_eq(v___x_370_, v___x_383_);
v___y_372_ = v___x_384_;
goto v___jp_371_;
}
v___jp_371_:
{
if (v___y_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
lean_del_object(v___x_344_);
v___x_373_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_374_ = lean_name_eq(v_declName_369_, v___x_373_);
lean_dec(v_declName_369_);
if (v___x_374_ == 0)
{
lean_dec(v___x_370_);
v___y_347_ = v___x_374_;
goto v___jp_346_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_dec_eq(v___x_370_, v___x_375_);
lean_dec(v___x_370_);
v___y_347_ = v___x_376_;
goto v___jp_346_;
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_dec(v___x_370_);
lean_dec(v_declName_369_);
lean_dec(v_a_342_);
lean_dec_ref(v_inst_334_);
v___x_377_ = lean_box(0);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_377_);
v___x_379_ = v___x_344_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v___x_368_);
lean_del_object(v___x_344_);
lean_dec_ref(v_inst_334_);
v___x_385_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_342_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_385_;
}
v___jp_346_:
{
if (v___y_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec_ref(v_inst_334_);
v___x_348_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_342_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = l_Lean_Expr_appArg_x21(v_a_342_);
lean_dec(v_a_342_);
v___x_350_ = l_Lean_Meta_reduceEval___redArg(v_inst_334_, v___x_349_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_359_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_a_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_350_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_350_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_inst_334_);
v_a_387_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_341_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_341_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___boxed(lean_object* v_00_u03b1_395_, lean_object* v_inst_396_, lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_instReduceEvalOption___private__1(v_00_u03b1_395_, v_inst_396_, v_e_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object* v_inst_404_, lean_object* v_e_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_411_ = lean_whnf(v_e_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_456_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_456_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_456_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_456_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___y_417_; lean_object* v___x_438_; 
v___x_438_ = l_Lean_Expr_getAppFn(v_a_412_);
if (lean_obj_tag(v___x_438_) == 4)
{
lean_object* v_declName_439_; lean_object* v___x_440_; uint8_t v___y_442_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_declName_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_declName_439_);
lean_dec_ref_known(v___x_438_, 2);
v___x_440_ = l_Lean_Expr_getAppNumArgs(v_a_412_);
v___x_451_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_452_ = lean_name_eq(v_declName_439_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_442_ = v___x_452_;
goto v___jp_441_;
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_nat_dec_eq(v___x_440_, v___x_453_);
v___y_442_ = v___x_454_;
goto v___jp_441_;
}
v___jp_441_:
{
if (v___y_442_ == 0)
{
lean_object* v___x_443_; uint8_t v___x_444_; 
lean_del_object(v___x_414_);
v___x_443_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_444_ = lean_name_eq(v_declName_439_, v___x_443_);
lean_dec(v_declName_439_);
if (v___x_444_ == 0)
{
lean_dec(v___x_440_);
v___y_417_ = v___x_444_;
goto v___jp_416_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_dec_eq(v___x_440_, v___x_445_);
lean_dec(v___x_440_);
v___y_417_ = v___x_446_;
goto v___jp_416_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_dec(v___x_440_);
lean_dec(v_declName_439_);
lean_dec(v_a_412_);
lean_dec_ref(v_inst_404_);
v___x_447_ = lean_box(0);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_447_);
v___x_449_ = v___x_414_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v___x_455_; 
lean_dec_ref(v___x_438_);
lean_del_object(v___x_414_);
lean_dec_ref(v_inst_404_);
v___x_455_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_412_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_455_;
}
v___jp_416_:
{
if (v___y_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec_ref(v_inst_404_);
v___x_418_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_412_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l_Lean_Expr_appArg_x21(v_a_412_);
lean_dec(v_a_412_);
v___x_420_ = l_Lean_Meta_reduceEval___redArg(v_inst_404_, v___x_419_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_420_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_inst_404_);
v_a_457_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_411_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_411_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(lean_object* v_inst_465_, lean_object* v_e_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(v_inst_465_, v_e_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object* v_inst_473_){
_start:
{
lean_object* v___f_474_; 
v___f_474_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_474_, 0, v_inst_473_);
return v___f_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* v_00_u03b1_475_, lean_object* v_inst_476_){
_start:
{
lean_object* v___f_477_; 
v___f_477_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_477_, 0, v_inst_476_);
return v___f_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1(lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; 
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc_ref(v_a_479_);
lean_inc_ref(v_e_478_);
v___x_484_ = lean_whnf(v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_496_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_496_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_496_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_496_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
if (lean_obj_tag(v_a_485_) == 9)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v_a_485_, 0);
lean_inc_ref(v_a_489_);
lean_dec_ref_known(v_a_485_, 1);
if (lean_obj_tag(v_a_489_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_492_; 
lean_dec_ref(v_e_478_);
v_val_490_ = lean_ctor_get(v_a_489_, 0);
lean_inc_ref(v_val_490_);
lean_dec_ref_known(v_a_489_, 1);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_val_490_);
v___x_492_ = v___x_487_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_val_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec_ref(v_a_489_);
lean_del_object(v___x_487_);
v___x_494_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_494_;
}
}
else
{
lean_object* v___x_495_; 
lean_del_object(v___x_487_);
lean_dec(v_a_485_);
v___x_495_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_495_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_e_478_);
v_a_497_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_484_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_484_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1___boxed(lean_object* v_e_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object* v_e_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc_ref(v_e_512_);
v___x_518_ = lean_whnf(v_e_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_530_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_530_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_530_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_530_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
if (lean_obj_tag(v_a_519_) == 9)
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v_a_519_, 0);
lean_inc_ref(v_a_523_);
lean_dec_ref_known(v_a_519_, 1);
if (lean_obj_tag(v_a_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_526_; 
lean_dec_ref(v_e_512_);
v_val_524_ = lean_ctor_get(v_a_523_, 0);
lean_inc_ref(v_val_524_);
lean_dec_ref_known(v_a_523_, 1);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v_val_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_val_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec_ref(v_a_523_);
lean_del_object(v___x_521_);
v___x_528_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; 
lean_del_object(v___x_521_);
lean_dec(v_a_519_);
v___x_529_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_529_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_e_512_);
v_a_531_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_518_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_518_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0___boxed(lean_object* v_e_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Meta_instReduceEvalString___lam__0(v_e_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___y_555_; lean_object* v___x_564_; uint8_t v_transparency_565_; uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_564_ = l_Lean_Meta_Context_config(v_a_549_);
v_transparency_565_ = lean_ctor_get_uint8(v___x_564_, 9);
lean_dec_ref(v___x_564_);
v___x_566_ = 1;
v___x_567_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_inc(v_a_552_);
lean_inc_ref(v_a_551_);
lean_inc(v_a_550_);
lean_inc_ref(v_a_549_);
v___x_568_ = lean_whnf(v_e_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_n(v_a_569_, 2);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = l_Lean_Meta_evalNat(v_a_569_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_580_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
if (lean_obj_tag(v_a_571_) == 1)
{
lean_object* v_val_575_; lean_object* v___x_577_; 
lean_dec(v_a_569_);
v_val_575_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_val_575_);
lean_dec_ref_known(v_a_571_, 1);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_val_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_val_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
else
{
lean_object* v___x_579_; 
lean_del_object(v___x_573_);
lean_dec(v_a_571_);
v___x_579_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_569_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
v___y_555_ = v___x_579_;
goto v___jp_554_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_a_569_);
v_a_581_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_570_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_570_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_568_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_568_);
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
else
{
lean_object* v_keyedConfig_597_; uint8_t v_trackZetaDelta_598_; lean_object* v_zetaDeltaSet_599_; lean_object* v_lctx_600_; lean_object* v_localInstances_601_; lean_object* v_defEqCtx_x3f_602_; lean_object* v_synthPendingDepth_603_; lean_object* v_customCanUnfoldPredicate_x3f_604_; uint8_t v_univApprox_605_; uint8_t v_inTypeClassResolution_606_; uint8_t v_cacheInferType_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_keyedConfig_597_ = lean_ctor_get(v_a_549_, 0);
v_trackZetaDelta_598_ = lean_ctor_get_uint8(v_a_549_, sizeof(void*)*7);
v_zetaDeltaSet_599_ = lean_ctor_get(v_a_549_, 1);
v_lctx_600_ = lean_ctor_get(v_a_549_, 2);
v_localInstances_601_ = lean_ctor_get(v_a_549_, 3);
v_defEqCtx_x3f_602_ = lean_ctor_get(v_a_549_, 4);
v_synthPendingDepth_603_ = lean_ctor_get(v_a_549_, 5);
v_customCanUnfoldPredicate_x3f_604_ = lean_ctor_get(v_a_549_, 6);
v_univApprox_605_ = lean_ctor_get_uint8(v_a_549_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_606_ = lean_ctor_get_uint8(v_a_549_, sizeof(void*)*7 + 2);
v_cacheInferType_607_ = lean_ctor_get_uint8(v_a_549_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_597_);
v___x_608_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_566_, v_keyedConfig_597_);
lean_inc(v_customCanUnfoldPredicate_x3f_604_);
lean_inc(v_synthPendingDepth_603_);
lean_inc(v_defEqCtx_x3f_602_);
lean_inc_ref(v_localInstances_601_);
lean_inc_ref(v_lctx_600_);
lean_inc(v_zetaDeltaSet_599_);
v___x_609_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v_zetaDeltaSet_599_);
lean_ctor_set(v___x_609_, 2, v_lctx_600_);
lean_ctor_set(v___x_609_, 3, v_localInstances_601_);
lean_ctor_set(v___x_609_, 4, v_defEqCtx_x3f_602_);
lean_ctor_set(v___x_609_, 5, v_synthPendingDepth_603_);
lean_ctor_set(v___x_609_, 6, v_customCanUnfoldPredicate_x3f_604_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*7, v_trackZetaDelta_598_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*7 + 1, v_univApprox_605_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*7 + 2, v_inTypeClassResolution_606_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*7 + 3, v_cacheInferType_607_);
lean_inc(v_a_552_);
lean_inc_ref(v_a_551_);
lean_inc(v_a_550_);
lean_inc_ref(v___x_609_);
v___x_610_ = lean_whnf(v_e_548_, v___x_609_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_n(v_a_611_, 2);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Meta_evalNat(v_a_611_, v___x_609_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_622_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
if (lean_obj_tag(v_a_613_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_619_; 
lean_dec(v_a_611_);
lean_dec_ref_known(v___x_609_, 7);
v_val_617_ = lean_ctor_get(v_a_613_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_a_613_, 1);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_val_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_val_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v___x_621_; 
lean_del_object(v___x_615_);
lean_dec(v_a_613_);
v___x_621_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_611_, v___x_609_, v_a_550_, v_a_551_, v_a_552_);
lean_dec_ref_known(v___x_609_, 7);
v___y_555_ = v___x_621_;
goto v___jp_554_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_611_);
lean_dec_ref_known(v___x_609_, 7);
v_a_623_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_612_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_612_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref_known(v___x_609_, 7);
v_a_631_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_610_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_610_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
v___jp_554_:
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___y_555_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___y_555_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___y_555_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___y_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object* v_e_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object* v_e_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___y_653_; lean_object* v___x_662_; uint8_t v_transparency_663_; uint8_t v___x_664_; uint8_t v___x_665_; 
v___x_662_ = l_Lean_Meta_Context_config(v_a_647_);
v_transparency_663_ = lean_ctor_get_uint8(v___x_662_, 9);
lean_dec_ref(v___x_662_);
v___x_664_ = 1;
v___x_665_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_inc(v_a_650_);
lean_inc_ref(v_a_649_);
lean_inc(v_a_648_);
lean_inc_ref(v_a_647_);
lean_inc_ref(v_e_646_);
v___x_666_ = lean_whnf(v_e_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_678_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
if (lean_obj_tag(v_a_667_) == 9)
{
lean_object* v_a_671_; 
v_a_671_ = lean_ctor_get(v_a_667_, 0);
lean_inc_ref(v_a_671_);
lean_dec_ref_known(v_a_667_, 1);
if (lean_obj_tag(v_a_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; 
lean_dec_ref(v_e_646_);
v_val_672_ = lean_ctor_get(v_a_671_, 0);
lean_inc_ref(v_val_672_);
lean_dec_ref_known(v_a_671_, 1);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v_val_672_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_val_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v_a_671_);
lean_del_object(v___x_669_);
v___x_676_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
v___y_653_ = v___x_676_;
goto v___jp_652_;
}
}
else
{
lean_object* v___x_677_; 
lean_del_object(v___x_669_);
lean_dec(v_a_667_);
v___x_677_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
v___y_653_ = v___x_677_;
goto v___jp_652_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_e_646_);
v_a_679_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_666_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_666_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_keyedConfig_687_; uint8_t v_trackZetaDelta_688_; lean_object* v_zetaDeltaSet_689_; lean_object* v_lctx_690_; lean_object* v_localInstances_691_; lean_object* v_defEqCtx_x3f_692_; lean_object* v_synthPendingDepth_693_; lean_object* v_customCanUnfoldPredicate_x3f_694_; uint8_t v_univApprox_695_; uint8_t v_inTypeClassResolution_696_; uint8_t v_cacheInferType_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_keyedConfig_687_ = lean_ctor_get(v_a_647_, 0);
v_trackZetaDelta_688_ = lean_ctor_get_uint8(v_a_647_, sizeof(void*)*7);
v_zetaDeltaSet_689_ = lean_ctor_get(v_a_647_, 1);
v_lctx_690_ = lean_ctor_get(v_a_647_, 2);
v_localInstances_691_ = lean_ctor_get(v_a_647_, 3);
v_defEqCtx_x3f_692_ = lean_ctor_get(v_a_647_, 4);
v_synthPendingDepth_693_ = lean_ctor_get(v_a_647_, 5);
v_customCanUnfoldPredicate_x3f_694_ = lean_ctor_get(v_a_647_, 6);
v_univApprox_695_ = lean_ctor_get_uint8(v_a_647_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_696_ = lean_ctor_get_uint8(v_a_647_, sizeof(void*)*7 + 2);
v_cacheInferType_697_ = lean_ctor_get_uint8(v_a_647_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_687_);
v___x_698_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_664_, v_keyedConfig_687_);
lean_inc(v_customCanUnfoldPredicate_x3f_694_);
lean_inc(v_synthPendingDepth_693_);
lean_inc(v_defEqCtx_x3f_692_);
lean_inc_ref(v_localInstances_691_);
lean_inc_ref(v_lctx_690_);
lean_inc(v_zetaDeltaSet_689_);
v___x_699_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_zetaDeltaSet_689_);
lean_ctor_set(v___x_699_, 2, v_lctx_690_);
lean_ctor_set(v___x_699_, 3, v_localInstances_691_);
lean_ctor_set(v___x_699_, 4, v_defEqCtx_x3f_692_);
lean_ctor_set(v___x_699_, 5, v_synthPendingDepth_693_);
lean_ctor_set(v___x_699_, 6, v_customCanUnfoldPredicate_x3f_694_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*7, v_trackZetaDelta_688_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*7 + 1, v_univApprox_695_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*7 + 2, v_inTypeClassResolution_696_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*7 + 3, v_cacheInferType_697_);
lean_inc(v_a_650_);
lean_inc_ref(v_a_649_);
lean_inc(v_a_648_);
lean_inc_ref(v___x_699_);
lean_inc_ref(v_e_646_);
v___x_700_ = lean_whnf(v_e_646_, v___x_699_, v_a_648_, v_a_649_, v_a_650_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_712_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_712_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_712_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_712_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
if (lean_obj_tag(v_a_701_) == 9)
{
lean_object* v_a_705_; 
v_a_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_a_705_);
lean_dec_ref_known(v_a_701_, 1);
if (lean_obj_tag(v_a_705_) == 1)
{
lean_object* v_val_706_; lean_object* v___x_708_; 
lean_dec_ref_known(v___x_699_, 7);
lean_dec_ref(v_e_646_);
v_val_706_ = lean_ctor_get(v_a_705_, 0);
lean_inc_ref(v_val_706_);
lean_dec_ref_known(v_a_705_, 1);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v_val_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_val_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v___x_710_; 
lean_dec_ref(v_a_705_);
lean_del_object(v___x_703_);
v___x_710_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_646_, v___x_699_, v_a_648_, v_a_649_, v_a_650_);
lean_dec_ref_known(v___x_699_, 7);
v___y_653_ = v___x_710_;
goto v___jp_652_;
}
}
else
{
lean_object* v___x_711_; 
lean_del_object(v___x_703_);
lean_dec(v_a_701_);
v___x_711_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_646_, v___x_699_, v_a_648_, v_a_649_, v_a_650_);
lean_dec_ref_known(v___x_699_, 7);
v___y_653_ = v___x_711_;
goto v___jp_652_;
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref_known(v___x_699_, 7);
lean_dec_ref(v_e_646_);
v_a_713_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_700_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_700_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
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
v___jp_652_:
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v_a_654_ = lean_ctor_get(v___y_653_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___y_653_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___y_653_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___y_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object* v_e_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_727_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object* v___x_728_, lean_object* v_00___729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(2u);
v___x_731_ = lean_nat_dec_eq(v___x_728_, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object* v___x_732_, lean_object* v_00___733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_732_, v_00___733_);
lean_dec(v___x_732_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* v_e_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; 
lean_inc(v_a_757_);
lean_inc_ref(v_a_756_);
lean_inc(v_a_755_);
lean_inc_ref(v_a_754_);
v___x_759_ = lean_whnf(v_e_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_841_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_841_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_841_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_841_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Expr_getAppFn(v_a_760_);
if (lean_obj_tag(v___x_764_) == 4)
{
lean_object* v_declName_765_; lean_object* v___x_766_; uint8_t v___y_768_; uint8_t v___y_796_; uint8_t v___y_827_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_declName_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_declName_765_);
lean_dec_ref_known(v___x_764_, 2);
v___x_766_ = l_Lean_Expr_getAppNumArgs(v_a_760_);
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7));
v___x_837_ = lean_name_eq(v_declName_765_, v___x_836_);
if (v___x_837_ == 0)
{
v___y_827_ = v___x_837_;
goto v___jp_826_;
}
else
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_nat_dec_eq(v___x_766_, v___x_838_);
v___y_827_ = v___x_839_;
goto v___jp_826_;
}
v___jp_767_:
{
if (v___y_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec(v___x_766_);
v___x_769_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_760_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_sub(v___x_766_, v___x_770_);
lean_dec(v___x_766_);
lean_inc(v___x_771_);
v___x_772_ = l_Lean_Expr_getRevArg_x21(v_a_760_, v___x_771_);
v___x_773_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_772_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v___x_775_ = lean_nat_sub(v___x_771_, v___x_770_);
lean_dec(v___x_771_);
v___x_776_ = l_Lean_Expr_getRevArg_x21(v_a_760_, v___x_775_);
lean_dec(v_a_760_);
v___x_777_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_776_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_Name_num___override(v_a_774_, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
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
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_774_);
v_a_787_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_777_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_dec(v___x_771_);
lean_dec(v_a_760_);
return v___x_773_;
}
}
}
v___jp_795_:
{
if (v___y_796_ == 0)
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3));
v___x_798_ = lean_name_eq(v_declName_765_, v___x_797_);
lean_dec(v_declName_765_);
if (v___x_798_ == 0)
{
v___y_768_ = v___x_798_;
goto v___jp_767_;
}
else
{
lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_766_, v___x_799_);
v___y_768_ = v___x_800_;
goto v___jp_767_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_declName_765_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_sub(v___x_766_, v___x_801_);
lean_dec(v___x_766_);
lean_inc(v___x_802_);
v___x_803_ = l_Lean_Expr_getRevArg_x21(v_a_760_, v___x_802_);
v___x_804_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_803_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v___x_806_ = lean_nat_sub(v___x_802_, v___x_801_);
lean_dec(v___x_802_);
v___x_807_ = l_Lean_Expr_getRevArg_x21(v_a_760_, v___x_806_);
lean_dec(v_a_760_);
v___x_808_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_807_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_817_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_Name_str___override(v_a_805_, v_a_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_a_805_);
v_a_818_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_808_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_808_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_dec(v___x_802_);
lean_dec(v_a_760_);
return v___x_804_;
}
}
}
v___jp_826_:
{
if (v___y_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
lean_del_object(v___x_762_);
v___x_828_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5));
v___x_829_ = lean_name_eq(v_declName_765_, v___x_828_);
if (v___x_829_ == 0)
{
v___y_796_ = v___x_829_;
goto v___jp_795_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_box(0);
v___x_831_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_766_, v___x_830_);
v___y_796_ = v___x_831_;
goto v___jp_795_;
}
}
else
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec(v___x_766_);
lean_dec(v_declName_765_);
lean_dec(v_a_760_);
v___x_832_ = lean_box(0);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_832_);
v___x_834_ = v___x_762_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v___x_764_);
lean_del_object(v___x_762_);
v___x_840_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_760_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
return v___x_840_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_759_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_759_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(lean_object* v_e_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1(lean_object* v_e_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1___boxed(lean_object* v_e_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Meta_instReduceEvalName___private__1(v_e_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(lean_object* v_inst_876_, lean_object* v_e_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
lean_inc(v_a_881_);
lean_inc_ref(v_a_880_);
lean_inc(v_a_879_);
lean_inc_ref(v_a_878_);
v___x_883_ = lean_whnf(v_e_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_945_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_945_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_945_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_945_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Expr_getAppFn(v_a_884_);
if (lean_obj_tag(v___x_888_) == 4)
{
lean_object* v_declName_889_; 
v_declName_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_declName_889_);
lean_dec_ref_known(v___x_888_, 2);
if (lean_obj_tag(v_declName_889_) == 1)
{
lean_object* v_pre_890_; 
v_pre_890_ = lean_ctor_get(v_declName_889_, 0);
lean_inc(v_pre_890_);
if (lean_obj_tag(v_pre_890_) == 1)
{
lean_object* v_pre_891_; 
v_pre_891_ = lean_ctor_get(v_pre_890_, 0);
if (lean_obj_tag(v_pre_891_) == 0)
{
lean_object* v_str_892_; lean_object* v_str_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_str_892_ = lean_ctor_get(v_declName_889_, 1);
lean_inc_ref(v_str_892_);
lean_dec_ref_known(v_declName_889_, 2);
v_str_893_ = lean_ctor_get(v_pre_890_, 1);
lean_inc_ref(v_str_893_);
lean_dec_ref_known(v_pre_890_, 2);
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0));
v___x_895_ = lean_string_dec_eq(v_str_893_, v___x_894_);
lean_dec_ref(v_str_893_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_str_892_);
lean_del_object(v___x_886_);
lean_dec_ref(v_inst_876_);
v___x_896_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_897_ = l_Lean_Expr_getAppNumArgs(v_a_884_);
v___x_898_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1));
v___x_899_ = lean_string_dec_eq(v_str_892_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; uint8_t v___x_901_; 
lean_del_object(v___x_886_);
v___x_900_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2));
v___x_901_ = lean_string_dec_eq(v_str_892_, v___x_900_);
lean_dec_ref(v_str_892_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v___x_897_);
lean_dec_ref(v_inst_876_);
v___x_902_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(3u);
v___x_904_ = lean_nat_dec_eq(v___x_897_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_dec(v___x_897_);
lean_dec_ref(v_inst_876_);
v___x_905_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_sub(v___x_897_, v___x_906_);
v___x_908_ = lean_nat_sub(v___x_907_, v___x_906_);
lean_dec(v___x_907_);
v___x_909_ = l_Lean_Expr_getRevArg_x21(v_a_884_, v___x_908_);
lean_inc_ref(v_inst_876_);
v___x_910_ = l_Lean_Meta_reduceEval___redArg(v_inst_876_, v___x_909_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = lean_unsigned_to_nat(2u);
v___x_913_ = lean_nat_sub(v___x_897_, v___x_912_);
lean_dec(v___x_897_);
v___x_914_ = lean_nat_sub(v___x_913_, v___x_906_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_Expr_getRevArg_x21(v_a_884_, v___x_914_);
lean_dec(v_a_884_);
v___x_916_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_876_, v___x_915_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_921_, 0, v_a_911_);
lean_ctor_set(v___x_921_, 1, v_a_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_923_ = v___x_919_;
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
else
{
lean_dec(v_a_911_);
return v___x_916_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___x_897_);
lean_dec(v_a_884_);
lean_dec_ref(v_inst_876_);
v_a_926_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_910_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_910_);
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
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
lean_dec_ref(v_str_892_);
lean_dec_ref(v_inst_876_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_dec_eq(v___x_897_, v___x_934_);
lean_dec(v___x_897_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_del_object(v___x_886_);
v___x_936_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_939_; 
lean_dec(v_a_884_);
v___x_937_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_937_);
v___x_939_ = v___x_886_;
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
else
{
lean_object* v___x_941_; 
lean_dec_ref_known(v_pre_890_, 2);
lean_dec_ref_known(v_declName_889_, 2);
lean_del_object(v___x_886_);
lean_dec_ref(v_inst_876_);
v___x_941_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_941_;
}
}
else
{
lean_object* v___x_942_; 
lean_dec_ref_known(v_declName_889_, 2);
lean_dec(v_pre_890_);
lean_del_object(v___x_886_);
lean_dec_ref(v_inst_876_);
v___x_942_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_942_;
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v_declName_889_);
lean_del_object(v___x_886_);
lean_dec_ref(v_inst_876_);
v___x_943_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_943_;
}
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v___x_888_);
lean_del_object(v___x_886_);
lean_dec_ref(v_inst_876_);
v___x_944_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_884_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_944_;
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v_inst_876_);
v_a_946_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_883_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_883_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(lean_object* v_inst_954_, lean_object* v_e_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_954_, v_e_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_e_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_963_, v_e_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(lean_object* v_00_u03b1_971_, lean_object* v_inst_972_, lean_object* v_e_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(v_00_u03b1_971_, v_inst_972_, v_e_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg(lean_object* v_inst_980_, lean_object* v_e_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_980_, v_e_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(lean_object* v_inst_988_, lean_object* v_e_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(v_inst_988_, v_e_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1(lean_object* v_00_u03b1_996_, lean_object* v_inst_997_, lean_object* v_e_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_997_, v_e_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Meta_instReduceEvalList___private__1(v_00_u03b1_1005_, v_inst_1006_, v_e_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___redArg(lean_object* v_inst_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_1015_, 0, lean_box(0));
lean_closure_set(v___x_1015_, 1, v_inst_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList(lean_object* v_00_u03b1_1016_, lean_object* v_inst_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_1018_, 0, lean_box(0));
lean_closure_set(v___x_1018_, 1, v_inst_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(lean_object* v_n_1024_, lean_object* v_e_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; 
lean_inc(v_a_1029_);
lean_inc_ref(v_a_1028_);
lean_inc(v_a_1027_);
lean_inc_ref(v_a_1026_);
v___x_1031_ = lean_whnf(v_e_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1034_ = lean_unsigned_to_nat(3u);
v___x_1035_ = l_Lean_Expr_isAppOfArity(v_a_1032_, v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1032_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
return v___x_1036_;
}
else
{
lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___f_1037_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = l_Lean_Expr_getAppNumArgs(v_a_1032_);
v___x_1040_ = lean_nat_sub(v___x_1039_, v___x_1038_);
lean_dec(v___x_1039_);
v___x_1041_ = lean_nat_sub(v___x_1040_, v___x_1038_);
lean_dec(v___x_1040_);
v___x_1042_ = l_Lean_Expr_getRevArg_x21(v_a_1032_, v___x_1041_);
lean_dec(v_a_1032_);
v___x_1043_ = l_Lean_Meta_reduceEval___redArg(v___f_1037_, v___x_1042_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_nat_mod(v_a_1044_, v_n_1024_);
lean_dec(v_a_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1043_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1043_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1031_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1031_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(lean_object* v_n_1069_, lean_object* v_e_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_1069_, v_e_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_n_1069_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(lean_object* v_n_1077_, lean_object* v_inst_1078_, lean_object* v_e_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
v___x_1085_ = lean_whnf(v_e_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1088_ = lean_unsigned_to_nat(3u);
v___x_1089_ = l_Lean_Expr_isAppOfArity(v_a_1086_, v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1086_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1090_;
}
else
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___f_1091_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
v___x_1094_ = lean_nat_sub(v___x_1093_, v___x_1092_);
lean_dec(v___x_1093_);
v___x_1095_ = lean_nat_sub(v___x_1094_, v___x_1092_);
lean_dec(v___x_1094_);
v___x_1096_ = l_Lean_Expr_getRevArg_x21(v_a_1086_, v___x_1095_);
lean_dec(v_a_1086_);
v___x_1097_ = l_Lean_Meta_reduceEval___redArg(v___f_1091_, v___x_1096_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1106_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_nat_mod(v_a_1098_, v_n_1077_);
lean_dec(v_a_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1097_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1097_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1085_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1085_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(lean_object* v_n_1123_, lean_object* v_inst_1124_, lean_object* v_e_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(v_n_1123_, v_inst_1124_, v_e_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_n_1123_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(lean_object* v_n_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1133_, 0, v_n_1132_);
lean_closure_set(v___x_1133_, 1, lean_box(0));
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat(lean_object* v_n_1134_, lean_object* v_inst_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1136_, 0, v_n_1134_);
lean_closure_set(v___x_1136_, 1, lean_box(0));
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1(lean_object* v_n_1142_, lean_object* v_e_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; 
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc(v_a_1145_);
lean_inc_ref(v_a_1144_);
v___x_1149_ = lean_whnf(v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2));
v___x_1152_ = lean_unsigned_to_nat(2u);
v___x_1153_ = l_Lean_Expr_isAppOfArity(v_a_1150_, v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1150_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1155_ = lean_nat_pow(v___x_1152_, v_n_1142_);
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_sub(v___x_1155_, v___x_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_nat_add(v___x_1157_, v___x_1156_);
lean_dec(v___x_1157_);
v___x_1159_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1159_, 0, v___x_1158_);
lean_closure_set(v___x_1159_, 1, lean_box(0));
v___x_1160_ = l_Lean_Expr_getAppNumArgs(v_a_1150_);
v___x_1161_ = lean_nat_sub(v___x_1160_, v___x_1156_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_nat_sub(v___x_1161_, v___x_1156_);
lean_dec(v___x_1161_);
v___x_1163_ = l_Lean_Expr_getRevArg_x21(v_a_1150_, v___x_1162_);
lean_dec(v_a_1150_);
v___x_1164_ = l_Lean_Meta_reduceEval___redArg(v___x_1159_, v___x_1163_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1164_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1164_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
v_a_1181_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1149_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1149_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(lean_object* v_n_1189_, lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_instReduceEvalBitVec___private__1(v_n_1189_, v_e_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_n_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec(lean_object* v_n_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalBitVec___private__1___boxed), 7, 1);
lean_closure_set(v___x_1198_, 0, v_n_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1(lean_object* v_e_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; 
lean_inc(v_a_1212_);
lean_inc_ref(v_a_1211_);
lean_inc(v_a_1210_);
lean_inc_ref(v_a_1209_);
v___x_1214_ = lean_whnf(v_e_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1232_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1232_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1232_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__2));
v___x_1220_ = l_Lean_Expr_isAppOf(v_a_1215_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__4));
v___x_1222_ = l_Lean_Expr_isAppOf(v_a_1215_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_del_object(v___x_1217_);
v___x_1223_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1215_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_dec(v_a_1215_);
v___x_1224_ = lean_box(v___x_1220_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1224_);
v___x_1226_ = v___x_1217_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec(v_a_1215_);
v___x_1228_ = lean_box(v___x_1220_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1228_);
v___x_1230_ = v___x_1217_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1214_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1214_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1___boxed(lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Meta_instReduceEvalBool___private__1(v_e_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1(lean_object* v_e_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___x_1261_; 
lean_inc(v_a_1259_);
lean_inc_ref(v_a_1258_);
lean_inc(v_a_1257_);
lean_inc_ref(v_a_1256_);
lean_inc_ref(v_e_1255_);
v___x_1261_ = lean_whnf(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1314_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1314_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1314_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Expr_constName_x3f(v_a_1262_);
lean_dec(v_a_1262_);
if (lean_obj_tag(v___x_1266_) == 1)
{
lean_object* v_val_1267_; 
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v___x_1266_, 1);
if (lean_obj_tag(v_val_1267_) == 1)
{
lean_object* v_pre_1268_; 
v_pre_1268_ = lean_ctor_get(v_val_1267_, 0);
lean_inc(v_pre_1268_);
if (lean_obj_tag(v_pre_1268_) == 1)
{
lean_object* v_pre_1269_; 
v_pre_1269_ = lean_ctor_get(v_pre_1268_, 0);
lean_inc(v_pre_1269_);
if (lean_obj_tag(v_pre_1269_) == 1)
{
lean_object* v_pre_1270_; 
v_pre_1270_ = lean_ctor_get(v_pre_1269_, 0);
if (lean_obj_tag(v_pre_1270_) == 0)
{
lean_object* v_str_1271_; lean_object* v_str_1272_; lean_object* v_str_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_str_1271_ = lean_ctor_get(v_val_1267_, 1);
lean_inc_ref(v_str_1271_);
lean_dec_ref_known(v_val_1267_, 2);
v_str_1272_ = lean_ctor_get(v_pre_1268_, 1);
lean_inc_ref(v_str_1272_);
lean_dec_ref_known(v_pre_1268_, 2);
v_str_1273_ = lean_ctor_get(v_pre_1269_, 1);
lean_inc_ref(v_str_1273_);
lean_dec_ref_known(v_pre_1269_, 2);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0));
v___x_1275_ = lean_string_dec_eq(v_str_1273_, v___x_1274_);
lean_dec_ref(v_str_1273_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref(v_str_1272_);
lean_dec_ref(v_str_1271_);
lean_del_object(v___x_1264_);
v___x_1276_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0));
v___x_1278_ = lean_string_dec_eq(v_str_1272_, v___x_1277_);
lean_dec_ref(v_str_1272_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec_ref(v_str_1271_);
lean_del_object(v___x_1264_);
v___x_1279_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1));
v___x_1281_ = lean_string_dec_eq(v_str_1271_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2));
v___x_1283_ = lean_string_dec_eq(v_str_1271_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3));
v___x_1285_ = lean_string_dec_eq(v_str_1271_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4));
v___x_1287_ = lean_string_dec_eq(v_str_1271_, v___x_1286_);
lean_dec_ref(v_str_1271_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_del_object(v___x_1264_);
v___x_1288_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1288_;
}
else
{
uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
lean_dec_ref(v_e_1255_);
v___x_1289_ = 3;
v___x_1290_ = lean_box(v___x_1289_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1290_);
v___x_1292_ = v___x_1264_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_dec_ref(v_str_1271_);
lean_dec_ref(v_e_1255_);
v___x_1294_ = 2;
v___x_1295_ = lean_box(v___x_1294_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1295_);
v___x_1297_ = v___x_1264_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec_ref(v_str_1271_);
lean_dec_ref(v_e_1255_);
v___x_1299_ = 1;
v___x_1300_ = lean_box(v___x_1299_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1300_);
v___x_1302_ = v___x_1264_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec_ref(v_str_1271_);
lean_dec_ref(v_e_1255_);
v___x_1304_ = 0;
v___x_1305_ = lean_box(v___x_1304_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1305_);
v___x_1307_ = v___x_1264_;
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
}
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref_known(v_pre_1269_, 2);
lean_dec_ref_known(v_pre_1268_, 2);
lean_dec_ref_known(v_val_1267_, 2);
lean_del_object(v___x_1264_);
v___x_1309_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1309_;
}
}
else
{
lean_object* v___x_1310_; 
lean_dec_ref_known(v_pre_1268_, 2);
lean_dec(v_pre_1269_);
lean_dec_ref_known(v_val_1267_, 2);
lean_del_object(v___x_1264_);
v___x_1310_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1311_; 
lean_dec(v_pre_1268_);
lean_dec_ref_known(v_val_1267_, 2);
lean_del_object(v___x_1264_);
v___x_1311_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; 
lean_dec(v_val_1267_);
lean_del_object(v___x_1264_);
v___x_1312_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1312_;
}
}
else
{
lean_object* v___x_1313_; 
lean_dec(v___x_1266_);
lean_del_object(v___x_1264_);
v___x_1313_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_e_1255_);
v_a_1315_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1261_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1261_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(lean_object* v_e_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(v_e_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1(lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; 
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
lean_inc(v_a_1345_);
lean_inc_ref(v_a_1344_);
v___x_1349_ = lean_whnf(v_e_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2));
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = l_Lean_Expr_isAppOfArity(v_a_1350_, v___x_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4));
v___x_1355_ = l_Lean_Expr_isAppOfArity(v_a_1350_, v___x_1354_, v___x_1352_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1350_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1356_;
}
else
{
lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___f_1357_ = ((lean_object*)(l_Lean_Meta_instReduceEvalString___closed__0));
v___x_1358_ = l_Lean_Expr_getAppNumArgs(v_a_1350_);
v___x_1359_ = lean_nat_sub(v___x_1358_, v___x_1352_);
lean_dec(v___x_1358_);
v___x_1360_ = l_Lean_Expr_getRevArg_x21(v_a_1350_, v___x_1359_);
lean_dec(v_a_1350_);
v___x_1361_ = l_Lean_Meta_reduceEval___redArg(v___f_1357_, v___x_1360_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1361_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1361_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___f_1379_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1380_ = l_Lean_Expr_getAppNumArgs(v_a_1350_);
v___x_1381_ = lean_nat_sub(v___x_1380_, v___x_1352_);
lean_dec(v___x_1380_);
v___x_1382_ = l_Lean_Expr_getRevArg_x21(v_a_1350_, v___x_1381_);
lean_dec(v_a_1350_);
v___x_1383_ = l_Lean_Meta_reduceEval___redArg(v___f_1379_, v___x_1382_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1392_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1383_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1383_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1349_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1349_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(lean_object* v_e_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Meta_instReduceEvalLiteral___private__1(v_e_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object* v_e_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1429_; 
lean_inc(v_a_1427_);
lean_inc_ref(v_a_1426_);
lean_inc(v_a_1425_);
lean_inc_ref(v_a_1424_);
v___x_1429_ = lean_whnf(v_e_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = l_Lean_Expr_isAppOfArity(v_a_1430_, v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1430_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1435_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1436_ = l_Lean_Expr_getAppNumArgs(v_a_1430_);
v___x_1437_ = lean_nat_sub(v___x_1436_, v___x_1432_);
lean_dec(v___x_1436_);
v___x_1438_ = l_Lean_Expr_getRevArg_x21(v_a_1430_, v___x_1437_);
lean_dec(v_a_1430_);
v___x_1439_ = l_Lean_Meta_reduceEval___redArg(v___x_1435_, v___x_1438_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
v_a_1448_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1439_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1439_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1429_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1429_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object* v_e_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_instReduceEvalMVarId___private__1(v_e_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0(lean_object* v_e_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
v___x_1477_ = lean_whnf(v_e_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = l_Lean_Expr_isAppOfArity(v_a_1478_, v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1478_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1483_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1484_ = l_Lean_Expr_getAppNumArgs(v_a_1478_);
v___x_1485_ = lean_nat_sub(v___x_1484_, v___x_1480_);
lean_dec(v___x_1484_);
v___x_1486_ = l_Lean_Expr_getRevArg_x21(v_a_1478_, v___x_1485_);
lean_dec(v_a_1478_);
v___x_1487_ = l_Lean_Meta_reduceEval___redArg(v___x_1483_, v___x_1486_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1487_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1487_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
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
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1477_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1477_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed(lean_object* v_e_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(v_e_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1(lean_object* v_e_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; 
lean_inc(v_a_1530_);
lean_inc_ref(v_a_1529_);
lean_inc(v_a_1528_);
lean_inc_ref(v_a_1527_);
v___x_1532_ = lean_whnf(v_e_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = l_Lean_Expr_isAppOfArity(v_a_1533_, v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1533_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1538_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1539_ = l_Lean_Expr_getAppNumArgs(v_a_1533_);
v___x_1540_ = lean_nat_sub(v___x_1539_, v___x_1535_);
lean_dec(v___x_1539_);
v___x_1541_ = l_Lean_Expr_getRevArg_x21(v_a_1533_, v___x_1540_);
lean_dec(v_a_1533_);
v___x_1542_ = l_Lean_Meta_reduceEval___redArg(v___x_1538_, v___x_1541_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_a_1551_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1542_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1542_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1532_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1532_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(lean_object* v_e_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(v_e_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(lean_object* v_e_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
v___x_1580_ = lean_whnf(v_e_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = l_Lean_Expr_isAppOfArity(v_a_1581_, v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1581_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1586_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1587_ = l_Lean_Expr_getAppNumArgs(v_a_1581_);
v___x_1588_ = lean_nat_sub(v___x_1587_, v___x_1583_);
lean_dec(v___x_1587_);
v___x_1589_ = l_Lean_Expr_getRevArg_x21(v_a_1581_, v___x_1588_);
lean_dec(v_a_1581_);
v___x_1590_ = l_Lean_Meta_reduceEval___redArg(v___x_1586_, v___x_1589_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1590_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1590_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1580_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1580_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed(lean_object* v_e_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(v_e_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1(lean_object* v_e_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc(v_a_1633_);
lean_inc_ref(v_a_1632_);
lean_inc(v_a_1631_);
lean_inc_ref(v_a_1630_);
v___x_1635_ = lean_whnf(v_e_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = l_Lean_Expr_isAppOfArity(v_a_1636_, v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1636_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1641_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1642_ = l_Lean_Expr_getAppNumArgs(v_a_1636_);
v___x_1643_ = lean_nat_sub(v___x_1642_, v___x_1638_);
lean_dec(v___x_1642_);
v___x_1644_ = l_Lean_Expr_getRevArg_x21(v_a_1636_, v___x_1643_);
lean_dec(v_a_1636_);
v___x_1645_ = l_Lean_Meta_reduceEval___redArg(v___x_1641_, v___x_1644_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_a_1654_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1645_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1645_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1635_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1635_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(lean_object* v_e_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_instReduceEvalFVarId___private__1(v_e_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0(lean_object* v_e_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
v___x_1683_ = lean_whnf(v_e_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v___x_1685_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = l_Lean_Expr_isAppOfArity(v_a_1684_, v___x_1685_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1684_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1689_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1690_ = l_Lean_Expr_getAppNumArgs(v_a_1684_);
v___x_1691_ = lean_nat_sub(v___x_1690_, v___x_1686_);
lean_dec(v___x_1690_);
v___x_1692_ = l_Lean_Expr_getRevArg_x21(v_a_1684_, v___x_1691_);
lean_dec(v_a_1684_);
v___x_1693_ = l_Lean_Meta_reduceEval___redArg(v___x_1689_, v___x_1692_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1693_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_a_1710_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1683_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1683_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed(lean_object* v_e_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(v_e_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ReduceEval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
