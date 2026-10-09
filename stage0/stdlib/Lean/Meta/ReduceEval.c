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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_reduceEval___redArg(lean_object* v_inst_1_, lean_object* v_e_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
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
LEAN_EXPORT void l_Lean_Meta_reduceEval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_e_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_reduceEval___redArg(v_inst_1_, v_e_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object* v_inst_46_, lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_reduceEval___redArg(v_inst_46_, v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_53_;
}
}
lean_object* l_Lean_Meta_reduceEval(lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_e_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_reduceEval___redArg(v_inst_55_, v_e_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_62_;
}
}
LEAN_EXPORT void l_Lean_Meta_reduceEval_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_55_ = stack[1].m_obj;
lean_object* v_e_56_ = stack[2].m_obj;
lean_object* v_a_57_ = stack[3].m_obj;
lean_object* v_a_58_ = stack[4].m_obj;
lean_object* v_a_59_ = stack[5].m_obj;
lean_object* v_a_60_ = stack[6].m_obj;
lean_object* v_res_63_;
v_res_63_ = l_Lean_Meta_reduceEval(lean_box(0), v_inst_55_, v_e_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_e_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_reduceEval(v_00_u03b1_64_, v_inst_65_, v_e_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
return v_res_72_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; lean_object* v_env_80_; uint8_t v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_toCold_84_; lean_object* v_mctx_85_; lean_object* v_lctx_86_; lean_object* v_options_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_79_ = lean_st_ref_get(v___y_77_);
v_env_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_env_80_);
lean_dec(v___x_79_);
v___x_81_ = 0;
v_env_82_ = l_Lean_Environment_setRecordingDeps(v_env_80_, v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_75_);
v_toCold_84_ = lean_ctor_get(v___y_76_, 0);
v_mctx_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_83_);
v_lctx_86_ = lean_ctor_get(v___y_74_, 2);
v_options_87_ = lean_ctor_get(v_toCold_84_, 2);
lean_inc_ref(v_options_87_);
lean_inc_ref(v_lctx_86_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_82_);
lean_ctor_set(v___x_88_, 1, v_mctx_85_);
lean_ctor_set(v___x_88_, 2, v_lctx_86_);
lean_ctor_set(v___x_88_, 3, v_options_87_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_73_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_73_ = stack[0].m_obj;
lean_object* v___y_74_ = stack[1].m_obj;
lean_object* v___y_75_ = stack[2].m_obj;
lean_object* v___y_76_ = stack[3].m_obj;
lean_object* v___y_77_ = stack[4].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(lean_object* v_msgData_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_98_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_ref_105_; lean_object* v___x_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_ref_105_ = lean_ctor_get(v___y_102_, 2);
v___x_106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
lean_inc(v_ref_105_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v_ref_105_);
lean_ctor_set(v___x_111_, 1, v_a_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 1);
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_99_ = stack[0].m_obj;
lean_object* v___y_100_ = stack[1].m_obj;
lean_object* v___y_101_ = stack[2].m_obj;
lean_object* v___y_102_ = stack[3].m_obj;
lean_object* v___y_103_ = stack[4].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1, &l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once, _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
v___x_134_ = l_Lean_indentExpr(v_e_127_);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_135_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_136_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_127_ = stack[0].m_obj;
lean_object* v_a_128_ = stack[1].m_obj;
lean_object* v_a_129_ = stack[2].m_obj;
lean_object* v_a_130_ = stack[3].m_obj;
lean_object* v_a_131_ = stack[4].m_obj;
lean_object* v_res_137_;
v_res_137_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_144_;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* v_00_u03b1_145_, lean_object* v_e_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_152_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_146_ = stack[1].m_obj;
lean_object* v_a_147_ = stack[2].m_obj;
lean_object* v_a_148_ = stack[3].m_obj;
lean_object* v_a_149_ = stack[4].m_obj;
lean_object* v_a_150_ = stack[5].m_obj;
lean_object* v_res_153_;
v_res_153_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_box(0), v_e_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* v_00_u03b1_154_, lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(v_00_u03b1_154_, v_e_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
return v_res_161_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_object* v_00_u03b1_162_, lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
return v___x_169_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_163_ = stack[1].m_obj;
lean_object* v___y_164_ = stack[2].m_obj;
lean_object* v___y_165_ = stack[3].m_obj;
lean_object* v___y_166_ = stack[4].m_obj;
lean_object* v___y_167_ = stack[5].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_box(0), v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(lean_object* v_00_u03b1_171_, lean_object* v_msg_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_171_, v_msg_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
lean_object* l_Lean_Meta_instReduceEvalNat___private__1(lean_object* v_e_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_185_; 
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
v___x_185_ = lean_whnf(v_e_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc_n(v_a_186_, 2);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = l_Lean_Meta_evalNat(v_a_186_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_197_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_197_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
if (lean_obj_tag(v_a_188_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_194_; 
lean_dec(v_a_186_);
v_val_192_ = lean_ctor_get(v_a_188_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_a_188_, 1);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v_val_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_val_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_196_; 
lean_del_object(v___x_190_);
lean_dec(v_a_188_);
v___x_196_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_186_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
return v___x_196_;
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_186_);
v_a_198_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_187_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_187_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_185_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_185_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalNat___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_179_ = stack[0].m_obj;
lean_object* v_a_180_ = stack[1].m_obj;
lean_object* v_a_181_ = stack[2].m_obj;
lean_object* v_a_182_ = stack[3].m_obj;
lean_object* v_a_183_ = stack[4].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1___boxed(lean_object* v_e_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_221_;
}
}
lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object* v_e_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
lean_inc(v___y_224_);
lean_inc_ref(v___y_223_);
v___x_228_ = lean_whnf(v_e_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_n(v_a_229_, 2);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = l_Lean_Meta_evalNat(v_a_229_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_240_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_240_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
if (lean_obj_tag(v_a_231_) == 1)
{
lean_object* v_val_235_; lean_object* v___x_237_; 
lean_dec(v_a_229_);
v_val_235_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_a_231_, 1);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v_val_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_val_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_object* v___x_239_; 
lean_del_object(v___x_233_);
lean_dec(v_a_231_);
v___x_239_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_229_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_239_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_a_229_);
v_a_241_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_230_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_230_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_a_249_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_228_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_228_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalNat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_222_ = stack[0].m_obj;
lean_object* v___y_223_ = stack[1].m_obj;
lean_object* v___y_224_ = stack[2].m_obj;
lean_object* v___y_225_ = stack[3].m_obj;
lean_object* v___y_226_ = stack[4].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Lean_Meta_instReduceEvalNat___lam__0(v_e_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0___boxed(lean_object* v_e_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_instReduceEvalNat___lam__0(v_e_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg(lean_object* v_inst_276_, lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; 
lean_inc(v_a_281_);
lean_inc_ref(v_a_280_);
lean_inc(v_a_279_);
lean_inc_ref(v_a_278_);
v___x_283_ = lean_whnf(v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_328_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_328_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_328_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_328_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint8_t v___y_289_; lean_object* v___x_310_; 
v___x_310_ = l_Lean_Expr_getAppFn(v_a_284_);
if (lean_obj_tag(v___x_310_) == 4)
{
lean_object* v_declName_311_; lean_object* v___x_312_; uint8_t v___y_314_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_declName_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_declName_311_);
lean_dec_ref_known(v___x_310_, 2);
v___x_312_ = l_Lean_Expr_getAppNumArgs(v_a_284_);
v___x_323_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_324_ = lean_name_eq(v_declName_311_, v___x_323_);
if (v___x_324_ == 0)
{
v___y_314_ = v___x_324_;
goto v___jp_313_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_nat_dec_eq(v___x_312_, v___x_325_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
v___jp_313_:
{
if (v___y_314_ == 0)
{
lean_object* v___x_315_; uint8_t v___x_316_; 
lean_del_object(v___x_286_);
v___x_315_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_316_ = lean_name_eq(v_declName_311_, v___x_315_);
lean_dec(v_declName_311_);
if (v___x_316_ == 0)
{
lean_dec(v___x_312_);
v___y_289_ = v___x_316_;
goto v___jp_288_;
}
else
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_dec_eq(v___x_312_, v___x_317_);
lean_dec(v___x_312_);
v___y_289_ = v___x_318_;
goto v___jp_288_;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v___x_312_);
lean_dec(v_declName_311_);
lean_dec(v_a_284_);
lean_dec_ref(v_inst_276_);
v___x_319_ = lean_box(0);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_319_);
v___x_321_ = v___x_286_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v___x_327_; 
lean_dec_ref(v___x_310_);
lean_del_object(v___x_286_);
lean_dec_ref(v_inst_276_);
v___x_327_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_284_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_327_;
}
v___jp_288_:
{
if (v___y_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec_ref(v_inst_276_);
v___x_290_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_284_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = l_Lean_Expr_appArg_x21(v_a_284_);
lean_dec(v_a_284_);
v___x_292_ = l_Lean_Meta_reduceEval___redArg(v_inst_276_, v___x_291_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_a_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_292_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_292_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_inst_276_);
v_a_329_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_283_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_283_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalOption___private__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_276_ = stack[0].m_obj;
lean_object* v_e_277_ = stack[1].m_obj;
lean_object* v_a_278_ = stack[2].m_obj;
lean_object* v_a_279_ = stack[3].m_obj;
lean_object* v_a_280_ = stack[4].m_obj;
lean_object* v_a_281_ = stack[5].m_obj;
lean_object* v_res_337_;
v_res_337_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(lean_object* v_inst_338_, lean_object* v_e_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_338_, v_e_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_345_;
}
}
lean_object* l_Lean_Meta_instReduceEvalOption___private__1(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_e_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
lean_inc(v_a_350_);
lean_inc_ref(v_a_349_);
v___x_354_ = lean_whnf(v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_399_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_399_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_399_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_399_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
uint8_t v___y_360_; lean_object* v___x_381_; 
v___x_381_ = l_Lean_Expr_getAppFn(v_a_355_);
if (lean_obj_tag(v___x_381_) == 4)
{
lean_object* v_declName_382_; lean_object* v___x_383_; uint8_t v___y_385_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_declName_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_declName_382_);
lean_dec_ref_known(v___x_381_, 2);
v___x_383_ = l_Lean_Expr_getAppNumArgs(v_a_355_);
v___x_394_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_395_ = lean_name_eq(v_declName_382_, v___x_394_);
if (v___x_395_ == 0)
{
v___y_385_ = v___x_395_;
goto v___jp_384_;
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_nat_dec_eq(v___x_383_, v___x_396_);
v___y_385_ = v___x_397_;
goto v___jp_384_;
}
v___jp_384_:
{
if (v___y_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
lean_del_object(v___x_357_);
v___x_386_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_387_ = lean_name_eq(v_declName_382_, v___x_386_);
lean_dec(v_declName_382_);
if (v___x_387_ == 0)
{
lean_dec(v___x_383_);
v___y_360_ = v___x_387_;
goto v___jp_359_;
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_dec_eq(v___x_383_, v___x_388_);
lean_dec(v___x_383_);
v___y_360_ = v___x_389_;
goto v___jp_359_;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_392_; 
lean_dec(v___x_383_);
lean_dec(v_declName_382_);
lean_dec(v_a_355_);
lean_dec_ref(v_inst_347_);
v___x_390_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_390_);
v___x_392_ = v___x_357_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
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
else
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_381_);
lean_del_object(v___x_357_);
lean_dec_ref(v_inst_347_);
v___x_398_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_355_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
return v___x_398_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; 
lean_dec_ref(v_inst_347_);
v___x_361_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_355_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_Expr_appArg_x21(v_a_355_);
lean_dec(v_a_355_);
v___x_363_ = l_Lean_Meta_reduceEval___redArg(v_inst_347_, v___x_362_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_372_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_a_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_363_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_363_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v_inst_347_);
v_a_400_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_354_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_354_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalOption___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_347_ = stack[1].m_obj;
lean_object* v_e_348_ = stack[2].m_obj;
lean_object* v_a_349_ = stack[3].m_obj;
lean_object* v_a_350_ = stack[4].m_obj;
lean_object* v_a_351_ = stack[5].m_obj;
lean_object* v_a_352_ = stack[6].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_Meta_instReduceEvalOption___private__1(lean_box(0), v_inst_347_, v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___boxed(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_instReduceEvalOption___private__1(v_00_u03b1_409_, v_inst_410_, v_e_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object* v_inst_418_, lean_object* v_e_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_425_ = lean_whnf(v_e_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_470_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_470_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_470_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_470_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___y_431_; lean_object* v___x_452_; 
v___x_452_ = l_Lean_Expr_getAppFn(v_a_426_);
if (lean_obj_tag(v___x_452_) == 4)
{
lean_object* v_declName_453_; lean_object* v___x_454_; uint8_t v___y_456_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_declName_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_declName_453_);
lean_dec_ref_known(v___x_452_, 2);
v___x_454_ = l_Lean_Expr_getAppNumArgs(v_a_426_);
v___x_465_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_466_ = lean_name_eq(v_declName_453_, v___x_465_);
if (v___x_466_ == 0)
{
v___y_456_ = v___x_466_;
goto v___jp_455_;
}
else
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_nat_dec_eq(v___x_454_, v___x_467_);
v___y_456_ = v___x_468_;
goto v___jp_455_;
}
v___jp_455_:
{
if (v___y_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
lean_del_object(v___x_428_);
v___x_457_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_458_ = lean_name_eq(v_declName_453_, v___x_457_);
lean_dec(v_declName_453_);
if (v___x_458_ == 0)
{
lean_dec(v___x_454_);
v___y_431_ = v___x_458_;
goto v___jp_430_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_dec_eq(v___x_454_, v___x_459_);
lean_dec(v___x_454_);
v___y_431_ = v___x_460_;
goto v___jp_430_;
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec(v___x_454_);
lean_dec(v_declName_453_);
lean_dec(v_a_426_);
lean_dec_ref(v_inst_418_);
v___x_461_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_461_);
v___x_463_ = v___x_428_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec_ref(v___x_452_);
lean_del_object(v___x_428_);
lean_dec_ref(v_inst_418_);
v___x_469_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_426_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_469_;
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec_ref(v_inst_418_);
v___x_432_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_426_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l_Lean_Expr_appArg_x21(v_a_426_);
lean_dec(v_a_426_);
v___x_434_ = l_Lean_Meta_reduceEval___redArg(v_inst_418_, v___x_433_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_a_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
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
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_434_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_434_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
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
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_inst_418_);
v_a_471_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_425_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_425_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalOption___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_418_ = stack[0].m_obj;
lean_object* v_e_419_ = stack[1].m_obj;
lean_object* v___y_420_ = stack[2].m_obj;
lean_object* v___y_421_ = stack[3].m_obj;
lean_object* v___y_422_ = stack[4].m_obj;
lean_object* v___y_423_ = stack[5].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(v_inst_418_, v_e_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(lean_object* v_inst_480_, lean_object* v_e_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(v_inst_480_, v_e_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object* v_inst_488_){
_start:
{
lean_object* v___f_489_; 
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_489_, 0, v_inst_488_);
return v___f_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v___f_492_; 
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_492_, 0, v_inst_491_);
return v___f_492_;
}
}
lean_object* l_Lean_Meta_instReduceEvalString___private__1(lean_object* v_e_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
lean_inc(v_a_497_);
lean_inc_ref(v_a_496_);
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
lean_inc_ref(v_e_493_);
v___x_499_ = lean_whnf(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_511_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_511_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_511_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_511_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
if (lean_obj_tag(v_a_500_) == 9)
{
lean_object* v_a_504_; 
v_a_504_ = lean_ctor_get(v_a_500_, 0);
lean_inc_ref(v_a_504_);
lean_dec_ref_known(v_a_500_, 1);
if (lean_obj_tag(v_a_504_) == 1)
{
lean_object* v_val_505_; lean_object* v___x_507_; 
lean_dec_ref(v_e_493_);
v_val_505_ = lean_ctor_get(v_a_504_, 0);
lean_inc_ref(v_val_505_);
lean_dec_ref_known(v_a_504_, 1);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v_val_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_val_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v___x_509_; 
lean_dec_ref(v_a_504_);
lean_del_object(v___x_502_);
v___x_509_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; 
lean_del_object(v___x_502_);
lean_dec(v_a_500_);
v___x_510_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_510_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_e_493_);
v_a_512_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_499_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_499_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalString___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_493_ = stack[0].m_obj;
lean_object* v_a_494_ = stack[1].m_obj;
lean_object* v_a_495_ = stack[2].m_obj;
lean_object* v_a_496_ = stack[3].m_obj;
lean_object* v_a_497_ = stack[4].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1___boxed(lean_object* v_e_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_527_;
}
}
lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object* v_e_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc_ref(v_e_528_);
v___x_534_ = lean_whnf(v_e_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_546_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_546_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
if (lean_obj_tag(v_a_535_) == 9)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v_a_535_, 0);
lean_inc_ref(v_a_539_);
lean_dec_ref_known(v_a_535_, 1);
if (lean_obj_tag(v_a_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_542_; 
lean_dec_ref(v_e_528_);
v_val_540_ = lean_ctor_get(v_a_539_, 0);
lean_inc_ref(v_val_540_);
lean_dec_ref_known(v_a_539_, 1);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_val_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_val_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v___x_544_; 
lean_dec_ref(v_a_539_);
lean_del_object(v___x_537_);
v___x_544_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; 
lean_del_object(v___x_537_);
lean_dec(v_a_535_);
v___x_545_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_545_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_e_528_);
v_a_547_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_534_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_534_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalString___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_528_ = stack[0].m_obj;
lean_object* v___y_529_ = stack[1].m_obj;
lean_object* v___y_530_ = stack[2].m_obj;
lean_object* v___y_531_ = stack[3].m_obj;
lean_object* v___y_532_ = stack[4].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Lean_Meta_instReduceEvalString___lam__0(v_e_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0___boxed(lean_object* v_e_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_instReduceEvalString___lam__0(v_e_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object* v_e_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___y_572_; lean_object* v___x_581_; uint8_t v_transparency_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_581_ = l_Lean_Meta_Context_config(v_a_566_);
v_transparency_582_ = lean_ctor_get_uint8(v___x_581_, 9);
lean_dec_ref(v___x_581_);
v___x_583_ = 1;
v___x_584_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_inc(v_a_569_);
lean_inc_ref(v_a_568_);
lean_inc(v_a_567_);
lean_inc_ref(v_a_566_);
v___x_585_ = lean_whnf(v_e_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_n(v_a_586_, 2);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = l_Lean_Meta_evalNat(v_a_586_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_597_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_597_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
if (lean_obj_tag(v_a_588_) == 1)
{
lean_object* v_val_592_; lean_object* v___x_594_; 
lean_dec(v_a_586_);
v_val_592_ = lean_ctor_get(v_a_588_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v_a_588_, 1);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_val_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_val_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_object* v___x_596_; 
lean_del_object(v___x_590_);
lean_dec(v_a_588_);
v___x_596_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_586_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
v___y_572_ = v___x_596_;
goto v___jp_571_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_586_);
v_a_598_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_587_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_587_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_a_606_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_585_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_585_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_keyedConfig_614_; uint8_t v_trackZetaDelta_615_; lean_object* v_zetaDeltaSet_616_; lean_object* v_lctx_617_; lean_object* v_localInstances_618_; lean_object* v_defEqCtx_x3f_619_; lean_object* v_synthPendingDepth_620_; lean_object* v_customCanUnfoldPredicate_x3f_621_; uint8_t v_univApprox_622_; uint8_t v_inTypeClassResolution_623_; uint8_t v_cacheInferType_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_keyedConfig_614_ = lean_ctor_get(v_a_566_, 0);
v_trackZetaDelta_615_ = lean_ctor_get_uint8(v_a_566_, sizeof(void*)*7);
v_zetaDeltaSet_616_ = lean_ctor_get(v_a_566_, 1);
v_lctx_617_ = lean_ctor_get(v_a_566_, 2);
v_localInstances_618_ = lean_ctor_get(v_a_566_, 3);
v_defEqCtx_x3f_619_ = lean_ctor_get(v_a_566_, 4);
v_synthPendingDepth_620_ = lean_ctor_get(v_a_566_, 5);
v_customCanUnfoldPredicate_x3f_621_ = lean_ctor_get(v_a_566_, 6);
v_univApprox_622_ = lean_ctor_get_uint8(v_a_566_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_623_ = lean_ctor_get_uint8(v_a_566_, sizeof(void*)*7 + 2);
v_cacheInferType_624_ = lean_ctor_get_uint8(v_a_566_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_614_);
v___x_625_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_583_, v_keyedConfig_614_);
lean_inc(v_customCanUnfoldPredicate_x3f_621_);
lean_inc(v_synthPendingDepth_620_);
lean_inc(v_defEqCtx_x3f_619_);
lean_inc_ref(v_localInstances_618_);
lean_inc_ref(v_lctx_617_);
lean_inc(v_zetaDeltaSet_616_);
v___x_626_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_zetaDeltaSet_616_);
lean_ctor_set(v___x_626_, 2, v_lctx_617_);
lean_ctor_set(v___x_626_, 3, v_localInstances_618_);
lean_ctor_set(v___x_626_, 4, v_defEqCtx_x3f_619_);
lean_ctor_set(v___x_626_, 5, v_synthPendingDepth_620_);
lean_ctor_set(v___x_626_, 6, v_customCanUnfoldPredicate_x3f_621_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*7, v_trackZetaDelta_615_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*7 + 1, v_univApprox_622_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*7 + 2, v_inTypeClassResolution_623_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*7 + 3, v_cacheInferType_624_);
lean_inc(v_a_569_);
lean_inc_ref(v_a_568_);
lean_inc(v_a_567_);
lean_inc_ref(v___x_626_);
v___x_627_ = lean_whnf(v_e_565_, v___x_626_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_n(v_a_628_, 2);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = l_Lean_Meta_evalNat(v_a_628_, v___x_626_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_639_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_639_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_639_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_639_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
if (lean_obj_tag(v_a_630_) == 1)
{
lean_object* v_val_634_; lean_object* v___x_636_; 
lean_dec(v_a_628_);
lean_dec_ref_known(v___x_626_, 7);
v_val_634_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v_a_630_, 1);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v_val_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_638_; 
lean_del_object(v___x_632_);
lean_dec(v_a_630_);
v___x_638_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_628_, v___x_626_, v_a_567_, v_a_568_, v_a_569_);
lean_dec_ref_known(v___x_626_, 7);
v___y_572_ = v___x_638_;
goto v___jp_571_;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_628_);
lean_dec_ref_known(v___x_626_, 7);
v_a_640_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_629_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_629_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref_known(v___x_626_, 7);
v_a_648_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_627_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_627_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
v___jp_571_:
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___y_572_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___y_572_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___y_572_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___y_572_);
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
LEAN_EXPORT void l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_565_ = stack[0].m_obj;
lean_object* v_a_566_ = stack[1].m_obj;
lean_object* v_a_567_ = stack[2].m_obj;
lean_object* v_a_568_ = stack[3].m_obj;
lean_object* v_a_569_ = stack[4].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object* v_e_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
return v_res_663_;
}
}
lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object* v_e_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___y_671_; lean_object* v___x_680_; uint8_t v_transparency_681_; uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_680_ = l_Lean_Meta_Context_config(v_a_665_);
v_transparency_681_ = lean_ctor_get_uint8(v___x_680_, 9);
lean_dec_ref(v___x_680_);
v___x_682_ = 1;
v___x_683_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_inc(v_a_668_);
lean_inc_ref(v_a_667_);
lean_inc(v_a_666_);
lean_inc_ref(v_a_665_);
lean_inc_ref(v_e_664_);
v___x_684_ = lean_whnf(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_696_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_696_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
if (lean_obj_tag(v_a_685_) == 9)
{
lean_object* v_a_689_; 
v_a_689_ = lean_ctor_get(v_a_685_, 0);
lean_inc_ref(v_a_689_);
lean_dec_ref_known(v_a_685_, 1);
if (lean_obj_tag(v_a_689_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_692_; 
lean_dec_ref(v_e_664_);
v_val_690_ = lean_ctor_get(v_a_689_, 0);
lean_inc_ref(v_val_690_);
lean_dec_ref_known(v_a_689_, 1);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_val_690_);
v___x_692_ = v___x_687_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_val_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
else
{
lean_object* v___x_694_; 
lean_dec_ref(v_a_689_);
lean_del_object(v___x_687_);
v___x_694_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_671_ = v___x_694_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_695_; 
lean_del_object(v___x_687_);
lean_dec(v_a_685_);
v___x_695_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_671_ = v___x_695_;
goto v___jp_670_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v_e_664_);
v_a_697_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_684_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_684_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
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
else
{
lean_object* v_keyedConfig_705_; uint8_t v_trackZetaDelta_706_; lean_object* v_zetaDeltaSet_707_; lean_object* v_lctx_708_; lean_object* v_localInstances_709_; lean_object* v_defEqCtx_x3f_710_; lean_object* v_synthPendingDepth_711_; lean_object* v_customCanUnfoldPredicate_x3f_712_; uint8_t v_univApprox_713_; uint8_t v_inTypeClassResolution_714_; uint8_t v_cacheInferType_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_keyedConfig_705_ = lean_ctor_get(v_a_665_, 0);
v_trackZetaDelta_706_ = lean_ctor_get_uint8(v_a_665_, sizeof(void*)*7);
v_zetaDeltaSet_707_ = lean_ctor_get(v_a_665_, 1);
v_lctx_708_ = lean_ctor_get(v_a_665_, 2);
v_localInstances_709_ = lean_ctor_get(v_a_665_, 3);
v_defEqCtx_x3f_710_ = lean_ctor_get(v_a_665_, 4);
v_synthPendingDepth_711_ = lean_ctor_get(v_a_665_, 5);
v_customCanUnfoldPredicate_x3f_712_ = lean_ctor_get(v_a_665_, 6);
v_univApprox_713_ = lean_ctor_get_uint8(v_a_665_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_714_ = lean_ctor_get_uint8(v_a_665_, sizeof(void*)*7 + 2);
v_cacheInferType_715_ = lean_ctor_get_uint8(v_a_665_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_705_);
v___x_716_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_682_, v_keyedConfig_705_);
lean_inc(v_customCanUnfoldPredicate_x3f_712_);
lean_inc(v_synthPendingDepth_711_);
lean_inc(v_defEqCtx_x3f_710_);
lean_inc_ref(v_localInstances_709_);
lean_inc_ref(v_lctx_708_);
lean_inc(v_zetaDeltaSet_707_);
v___x_717_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_zetaDeltaSet_707_);
lean_ctor_set(v___x_717_, 2, v_lctx_708_);
lean_ctor_set(v___x_717_, 3, v_localInstances_709_);
lean_ctor_set(v___x_717_, 4, v_defEqCtx_x3f_710_);
lean_ctor_set(v___x_717_, 5, v_synthPendingDepth_711_);
lean_ctor_set(v___x_717_, 6, v_customCanUnfoldPredicate_x3f_712_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*7, v_trackZetaDelta_706_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*7 + 1, v_univApprox_713_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*7 + 2, v_inTypeClassResolution_714_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*7 + 3, v_cacheInferType_715_);
lean_inc(v_a_668_);
lean_inc_ref(v_a_667_);
lean_inc(v_a_666_);
lean_inc_ref(v___x_717_);
lean_inc_ref(v_e_664_);
v___x_718_ = lean_whnf(v_e_664_, v___x_717_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_730_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_730_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_730_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
if (lean_obj_tag(v_a_719_) == 9)
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_a_723_);
lean_dec_ref_known(v_a_719_, 1);
if (lean_obj_tag(v_a_723_) == 1)
{
lean_object* v_val_724_; lean_object* v___x_726_; 
lean_dec_ref_known(v___x_717_, 7);
lean_dec_ref(v_e_664_);
v_val_724_ = lean_ctor_get(v_a_723_, 0);
lean_inc_ref(v_val_724_);
lean_dec_ref_known(v_a_723_, 1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_val_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_val_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v___x_728_; 
lean_dec_ref(v_a_723_);
lean_del_object(v___x_721_);
v___x_728_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_664_, v___x_717_, v_a_666_, v_a_667_, v_a_668_);
lean_dec_ref_known(v___x_717_, 7);
v___y_671_ = v___x_728_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_729_; 
lean_del_object(v___x_721_);
lean_dec(v_a_719_);
v___x_729_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_664_, v___x_717_, v_a_666_, v_a_667_, v_a_668_);
lean_dec_ref_known(v___x_717_, 7);
v___y_671_ = v___x_729_;
goto v___jp_670_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref_known(v___x_717_, 7);
lean_dec_ref(v_e_664_);
v_a_731_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_718_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_718_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
v___jp_670_:
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___y_671_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___y_671_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___y_671_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___y_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_664_ = stack[0].m_obj;
lean_object* v_a_665_ = stack[1].m_obj;
lean_object* v_a_666_ = stack[2].m_obj;
lean_object* v_a_667_ = stack[3].m_obj;
lean_object* v_a_668_ = stack[4].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object* v_e_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_746_;
}
}
uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object* v___x_747_, lean_object* v_00___748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(2u);
v___x_750_ = lean_nat_dec_eq(v___x_747_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_747_ = stack[0].m_obj;
lean_object* v_00___748_ = stack[1].m_obj;
uint8_t v_res_751_;
v_res_751_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_747_, v_00___748_);
stack->m_num = v_res_751_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object* v___x_752_, lean_object* v_00___753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_752_, v_00___753_);
lean_dec(v___x_752_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* v_e_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; 
lean_inc(v_a_777_);
lean_inc_ref(v_a_776_);
lean_inc(v_a_775_);
lean_inc_ref(v_a_774_);
v___x_779_ = lean_whnf(v_e_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_861_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_861_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_861_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_861_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Expr_getAppFn(v_a_780_);
if (lean_obj_tag(v___x_784_) == 4)
{
lean_object* v_declName_785_; lean_object* v___x_786_; uint8_t v___y_788_; uint8_t v___y_816_; uint8_t v___y_847_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_declName_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_declName_785_);
lean_dec_ref_known(v___x_784_, 2);
v___x_786_ = l_Lean_Expr_getAppNumArgs(v_a_780_);
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7));
v___x_857_ = lean_name_eq(v_declName_785_, v___x_856_);
if (v___x_857_ == 0)
{
v___y_847_ = v___x_857_;
goto v___jp_846_;
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_nat_dec_eq(v___x_786_, v___x_858_);
v___y_847_ = v___x_859_;
goto v___jp_846_;
}
v___jp_787_:
{
if (v___y_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v___x_786_);
v___x_789_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_780_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_sub(v___x_786_, v___x_790_);
lean_dec(v___x_786_);
lean_inc(v___x_791_);
v___x_792_ = l_Lean_Expr_getRevArg_x21(v_a_780_, v___x_791_);
v___x_793_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_792_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = lean_nat_sub(v___x_791_, v___x_790_);
lean_dec(v___x_791_);
v___x_796_ = l_Lean_Expr_getRevArg_x21(v_a_780_, v___x_795_);
lean_dec(v_a_780_);
v___x_797_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_796_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l_Lean_Name_num___override(v_a_794_, v_a_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_a_794_);
v_a_807_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_797_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_dec(v___x_791_);
lean_dec(v_a_780_);
return v___x_793_;
}
}
}
v___jp_815_:
{
if (v___y_816_ == 0)
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3));
v___x_818_ = lean_name_eq(v_declName_785_, v___x_817_);
lean_dec(v_declName_785_);
if (v___x_818_ == 0)
{
v___y_788_ = v___x_818_;
goto v___jp_787_;
}
else
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_box(0);
v___x_820_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_786_, v___x_819_);
v___y_788_ = v___x_820_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_declName_785_);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_sub(v___x_786_, v___x_821_);
lean_dec(v___x_786_);
lean_inc(v___x_822_);
v___x_823_ = l_Lean_Expr_getRevArg_x21(v_a_780_, v___x_822_);
v___x_824_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_823_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = lean_nat_sub(v___x_822_, v___x_821_);
lean_dec(v___x_822_);
v___x_827_ = l_Lean_Expr_getRevArg_x21(v_a_780_, v___x_826_);
lean_dec(v_a_780_);
v___x_828_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_827_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_837_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_837_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = l_Lean_Name_str___override(v_a_825_, v_a_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_833_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_a_825_);
v_a_838_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_828_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_828_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_dec(v___x_822_);
lean_dec(v_a_780_);
return v___x_824_;
}
}
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
lean_del_object(v___x_782_);
v___x_848_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5));
v___x_849_ = lean_name_eq(v_declName_785_, v___x_848_);
if (v___x_849_ == 0)
{
v___y_816_ = v___x_849_;
goto v___jp_815_;
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_box(0);
v___x_851_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_786_, v___x_850_);
v___y_816_ = v___x_851_;
goto v___jp_815_;
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_dec(v___x_786_);
lean_dec(v_declName_785_);
lean_dec(v_a_780_);
v___x_852_ = lean_box(0);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_852_);
v___x_854_ = v___x_782_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v___x_860_; 
lean_dec_ref(v___x_784_);
lean_del_object(v___x_782_);
v___x_860_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_780_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v___x_860_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_779_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_779_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_773_ = stack[0].m_obj;
lean_object* v_a_774_ = stack[1].m_obj;
lean_object* v_a_775_ = stack[2].m_obj;
lean_object* v_a_776_ = stack[3].m_obj;
lean_object* v_a_777_ = stack[4].m_obj;
lean_object* v_res_870_;
v_res_870_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(lean_object* v_e_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_877_;
}
}
lean_object* l_Lean_Meta_instReduceEvalName___private__1(lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_884_;
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalName___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_878_ = stack[0].m_obj;
lean_object* v_a_879_ = stack[1].m_obj;
lean_object* v_a_880_ = stack[2].m_obj;
lean_object* v_a_881_ = stack[3].m_obj;
lean_object* v_a_882_ = stack[4].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_Meta_instReduceEvalName___private__1(v_e_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1___boxed(lean_object* v_e_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Meta_instReduceEvalName___private__1(v_e_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_892_;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(lean_object* v_inst_898_, lean_object* v_e_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; 
lean_inc(v_a_903_);
lean_inc_ref(v_a_902_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
v___x_905_ = lean_whnf(v_e_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_967_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_967_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_967_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_967_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Expr_getAppFn(v_a_906_);
if (lean_obj_tag(v___x_910_) == 4)
{
lean_object* v_declName_911_; 
v_declName_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_declName_911_);
lean_dec_ref_known(v___x_910_, 2);
if (lean_obj_tag(v_declName_911_) == 1)
{
lean_object* v_pre_912_; 
v_pre_912_ = lean_ctor_get(v_declName_911_, 0);
lean_inc(v_pre_912_);
if (lean_obj_tag(v_pre_912_) == 1)
{
lean_object* v_pre_913_; 
v_pre_913_ = lean_ctor_get(v_pre_912_, 0);
if (lean_obj_tag(v_pre_913_) == 0)
{
lean_object* v_str_914_; lean_object* v_str_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_str_914_ = lean_ctor_get(v_declName_911_, 1);
lean_inc_ref(v_str_914_);
lean_dec_ref_known(v_declName_911_, 2);
v_str_915_ = lean_ctor_get(v_pre_912_, 1);
lean_inc_ref(v_str_915_);
lean_dec_ref_known(v_pre_912_, 2);
v___x_916_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0));
v___x_917_ = lean_string_dec_eq(v_str_915_, v___x_916_);
lean_dec_ref(v_str_915_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
lean_dec_ref(v_str_914_);
lean_del_object(v___x_908_);
lean_dec_ref(v_inst_898_);
v___x_918_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = l_Lean_Expr_getAppNumArgs(v_a_906_);
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1));
v___x_921_ = lean_string_dec_eq(v_str_914_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
lean_del_object(v___x_908_);
v___x_922_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2));
v___x_923_ = lean_string_dec_eq(v_str_914_, v___x_922_);
lean_dec_ref(v_str_914_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec(v___x_919_);
lean_dec_ref(v_inst_898_);
v___x_924_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(3u);
v___x_926_ = lean_nat_dec_eq(v___x_919_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec(v___x_919_);
lean_dec_ref(v_inst_898_);
v___x_927_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_sub(v___x_919_, v___x_928_);
v___x_930_ = lean_nat_sub(v___x_929_, v___x_928_);
lean_dec(v___x_929_);
v___x_931_ = l_Lean_Expr_getRevArg_x21(v_a_906_, v___x_930_);
lean_inc_ref(v_inst_898_);
v___x_932_ = l_Lean_Meta_reduceEval___redArg(v_inst_898_, v___x_931_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_unsigned_to_nat(2u);
v___x_935_ = lean_nat_sub(v___x_919_, v___x_934_);
lean_dec(v___x_919_);
v___x_936_ = lean_nat_sub(v___x_935_, v___x_928_);
lean_dec(v___x_935_);
v___x_937_ = l_Lean_Expr_getRevArg_x21(v_a_906_, v___x_936_);
lean_dec(v_a_906_);
v___x_938_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_898_, v___x_937_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_a_933_);
lean_ctor_set(v___x_943_, 1, v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_dec(v_a_933_);
return v___x_938_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v___x_919_);
lean_dec(v_a_906_);
lean_dec_ref(v_inst_898_);
v_a_948_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_932_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_932_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
else
{
lean_object* v___x_956_; uint8_t v___x_957_; 
lean_dec_ref(v_str_914_);
lean_dec_ref(v_inst_898_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_dec_eq(v___x_919_, v___x_956_);
lean_dec(v___x_919_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_del_object(v___x_908_);
v___x_958_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec(v_a_906_);
v___x_959_ = lean_box(0);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_959_);
v___x_961_ = v___x_908_;
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
else
{
lean_object* v___x_963_; 
lean_dec_ref_known(v_pre_912_, 2);
lean_dec_ref_known(v_declName_911_, 2);
lean_del_object(v___x_908_);
lean_dec_ref(v_inst_898_);
v___x_963_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v_pre_912_);
lean_dec_ref_known(v_declName_911_, 2);
lean_del_object(v___x_908_);
lean_dec_ref(v_inst_898_);
v___x_964_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_964_;
}
}
else
{
lean_object* v___x_965_; 
lean_dec(v_declName_911_);
lean_del_object(v___x_908_);
lean_dec_ref(v_inst_898_);
v___x_965_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_965_;
}
}
else
{
lean_object* v___x_966_; 
lean_dec_ref(v___x_910_);
lean_del_object(v___x_908_);
lean_dec_ref(v_inst_898_);
v___x_966_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_966_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v_inst_898_);
v_a_968_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_905_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_905_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_898_ = stack[0].m_obj;
lean_object* v_e_899_ = stack[1].m_obj;
lean_object* v_a_900_ = stack[2].m_obj;
lean_object* v_a_901_ = stack[3].m_obj;
lean_object* v_a_902_ = stack[4].m_obj;
lean_object* v_a_903_ = stack[5].m_obj;
lean_object* v_res_976_;
v_res_976_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_898_, v_e_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(lean_object* v_inst_977_, lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_977_, v_e_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_984_;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_object* v_00_u03b1_985_, lean_object* v_inst_986_, lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_986_, v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_993_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_986_ = stack[1].m_obj;
lean_object* v_e_987_ = stack[2].m_obj;
lean_object* v_a_988_ = stack[3].m_obj;
lean_object* v_a_989_ = stack[4].m_obj;
lean_object* v_a_990_ = stack[5].m_obj;
lean_object* v_a_991_ = stack[6].m_obj;
lean_object* v_res_994_;
v_res_994_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_box(0), v_inst_986_, v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(lean_object* v_00_u03b1_995_, lean_object* v_inst_996_, lean_object* v_e_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(v_00_u03b1_995_, v_inst_996_, v_e_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1003_;
}
}
lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg(lean_object* v_inst_1004_, lean_object* v_e_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_1004_, v_e_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalList___private__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1004_ = stack[0].m_obj;
lean_object* v_e_1005_ = stack[1].m_obj;
lean_object* v_a_1006_ = stack[2].m_obj;
lean_object* v_a_1007_ = stack[3].m_obj;
lean_object* v_a_1008_ = stack[4].m_obj;
lean_object* v_a_1009_ = stack[5].m_obj;
lean_object* v_res_1012_;
v_res_1012_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(v_inst_1004_, v_e_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
stack->m_obj
 = v_res_1012_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(lean_object* v_inst_1013_, lean_object* v_e_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(v_inst_1013_, v_e_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1020_;
}
}
lean_object* l_Lean_Meta_instReduceEvalList___private__1(lean_object* v_00_u03b1_1021_, lean_object* v_inst_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_1022_, v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalList___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1022_ = stack[1].m_obj;
lean_object* v_e_1023_ = stack[2].m_obj;
lean_object* v_a_1024_ = stack[3].m_obj;
lean_object* v_a_1025_ = stack[4].m_obj;
lean_object* v_a_1026_ = stack[5].m_obj;
lean_object* v_a_1027_ = stack[6].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l_Lean_Meta_instReduceEvalList___private__1(lean_box(0), v_inst_1022_, v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_inst_1032_, lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_instReduceEvalList___private__1(v_00_u03b1_1031_, v_inst_1032_, v_e_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___redArg(lean_object* v_inst_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_1041_, 0, lean_box(0));
lean_closure_set(v___x_1041_, 1, v_inst_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList(lean_object* v_00_u03b1_1042_, lean_object* v_inst_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_1044_, 0, lean_box(0));
lean_closure_set(v___x_1044_, 1, v_inst_1043_);
return v___x_1044_;
}
}
lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(lean_object* v_n_1050_, lean_object* v_e_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; 
v___f_1057_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
v___x_1058_ = lean_whnf(v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1061_ = lean_unsigned_to_nat(3u);
v___x_1062_ = l_Lean_Expr_isAppOfArity(v_a_1059_, v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1059_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = l_Lean_Expr_getAppNumArgs(v_a_1059_);
v___x_1066_ = lean_nat_sub(v___x_1065_, v___x_1064_);
lean_dec(v___x_1065_);
v___x_1067_ = lean_nat_sub(v___x_1066_, v___x_1064_);
lean_dec(v___x_1066_);
v___x_1068_ = l_Lean_Expr_getRevArg_x21(v_a_1059_, v___x_1067_);
lean_dec(v_a_1059_);
v___x_1069_ = l_Lean_Meta_reduceEval___redArg(v___f_1057_, v___x_1068_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_nat_mod(v_a_1070_, v_n_1050_);
lean_dec(v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
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
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1069_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1069_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1058_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1058_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1050_ = stack[0].m_obj;
lean_object* v_e_1051_ = stack[1].m_obj;
lean_object* v_a_1052_ = stack[2].m_obj;
lean_object* v_a_1053_ = stack[3].m_obj;
lean_object* v_a_1054_ = stack[4].m_obj;
lean_object* v_a_1055_ = stack[5].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_1050_, v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(lean_object* v_n_1096_, lean_object* v_e_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_1096_, v_e_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_n_1096_);
return v_res_1103_;
}
}
lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(lean_object* v_n_1104_, lean_object* v_inst_1105_, lean_object* v_e_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___f_1112_; lean_object* v___x_1113_; 
v___f_1112_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
v___x_1113_ = lean_whnf(v_e_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1116_ = lean_unsigned_to_nat(3u);
v___x_1117_ = l_Lean_Expr_isAppOfArity(v_a_1114_, v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1114_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = l_Lean_Expr_getAppNumArgs(v_a_1114_);
v___x_1121_ = lean_nat_sub(v___x_1120_, v___x_1119_);
lean_dec(v___x_1120_);
v___x_1122_ = lean_nat_sub(v___x_1121_, v___x_1119_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_Expr_getRevArg_x21(v_a_1114_, v___x_1122_);
lean_dec(v_a_1114_);
v___x_1124_ = l_Lean_Meta_reduceEval___redArg(v___f_1112_, v___x_1123_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_nat_mod(v_a_1125_, v_n_1104_);
lean_dec(v_a_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1129_);
v___x_1131_ = v___x_1127_;
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
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1124_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1124_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1113_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1113_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
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
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1104_ = stack[0].m_obj;
lean_object* v_e_1106_ = stack[2].m_obj;
lean_object* v_a_1107_ = stack[3].m_obj;
lean_object* v_a_1108_ = stack[4].m_obj;
lean_object* v_a_1109_ = stack[5].m_obj;
lean_object* v_a_1110_ = stack[6].m_obj;
lean_object* v_res_1150_;
v_res_1150_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(v_n_1104_, lean_box(0), v_e_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
stack->m_obj
 = v_res_1150_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(lean_object* v_n_1151_, lean_object* v_inst_1152_, lean_object* v_e_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(v_n_1151_, v_inst_1152_, v_e_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_n_1151_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(lean_object* v_n_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1161_, 0, v_n_1160_);
lean_closure_set(v___x_1161_, 1, lean_box(0));
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat(lean_object* v_n_1162_, lean_object* v_inst_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1164_, 0, v_n_1162_);
lean_closure_set(v___x_1164_, 1, lean_box(0));
return v___x_1164_;
}
}
lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1(lean_object* v_n_1170_, lean_object* v_e_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; 
lean_inc(v_a_1175_);
lean_inc_ref(v_a_1174_);
lean_inc(v_a_1173_);
lean_inc_ref(v_a_1172_);
v___x_1177_ = lean_whnf(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2));
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = l_Lean_Expr_isAppOfArity(v_a_1178_, v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1178_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1183_ = lean_nat_pow(v___x_1180_, v_n_1170_);
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_nat_sub(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_nat_add(v___x_1185_, v___x_1184_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1187_, 0, v___x_1186_);
lean_closure_set(v___x_1187_, 1, lean_box(0));
v___x_1188_ = l_Lean_Expr_getAppNumArgs(v_a_1178_);
v___x_1189_ = lean_nat_sub(v___x_1188_, v___x_1184_);
lean_dec(v___x_1188_);
v___x_1190_ = lean_nat_sub(v___x_1189_, v___x_1184_);
lean_dec(v___x_1189_);
v___x_1191_ = l_Lean_Expr_getRevArg_x21(v_a_1178_, v___x_1190_);
lean_dec(v_a_1178_);
v___x_1192_ = l_Lean_Meta_reduceEval___redArg(v___x_1187_, v___x_1191_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1192_);
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
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1177_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1177_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalBitVec___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1170_ = stack[0].m_obj;
lean_object* v_e_1171_ = stack[1].m_obj;
lean_object* v_a_1172_ = stack[2].m_obj;
lean_object* v_a_1173_ = stack[3].m_obj;
lean_object* v_a_1174_ = stack[4].m_obj;
lean_object* v_a_1175_ = stack[5].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l_Lean_Meta_instReduceEvalBitVec___private__1(v_n_1170_, v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(lean_object* v_n_1218_, lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Meta_instReduceEvalBitVec___private__1(v_n_1218_, v_e_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_n_1218_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec(lean_object* v_n_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalBitVec___private__1___boxed), 7, 1);
lean_closure_set(v___x_1227_, 0, v_n_1226_);
return v___x_1227_;
}
}
lean_object* l_Lean_Meta_instReduceEvalBool___private__1(lean_object* v_e_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; 
lean_inc(v_a_1241_);
lean_inc_ref(v_a_1240_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
v___x_1243_ = lean_whnf(v_e_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1261_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1261_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1261_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__2));
v___x_1249_ = l_Lean_Expr_isAppOf(v_a_1244_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__4));
v___x_1251_ = l_Lean_Expr_isAppOf(v_a_1244_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_del_object(v___x_1246_);
v___x_1252_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1244_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec(v_a_1244_);
v___x_1253_ = lean_box(v___x_1249_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1253_);
v___x_1255_ = v___x_1246_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_dec(v_a_1244_);
v___x_1257_ = lean_box(v___x_1249_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1257_);
v___x_1259_ = v___x_1246_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1262_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1243_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1243_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalBool___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1237_ = stack[0].m_obj;
lean_object* v_a_1238_ = stack[1].m_obj;
lean_object* v_a_1239_ = stack[2].m_obj;
lean_object* v_a_1240_ = stack[3].m_obj;
lean_object* v_a_1241_ = stack[4].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_Meta_instReduceEvalBool___private__1(v_e_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1___boxed(lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Meta_instReduceEvalBool___private__1(v_e_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
return v_res_1277_;
}
}
lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1(lean_object* v_e_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; 
lean_inc(v_a_1289_);
lean_inc_ref(v_a_1288_);
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
lean_inc_ref(v_e_1285_);
v___x_1291_ = lean_whnf(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1344_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1344_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1344_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Expr_constName_x3f(v_a_1292_);
lean_dec(v_a_1292_);
if (lean_obj_tag(v___x_1296_) == 1)
{
lean_object* v_val_1297_; 
v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1296_, 1);
if (lean_obj_tag(v_val_1297_) == 1)
{
lean_object* v_pre_1298_; 
v_pre_1298_ = lean_ctor_get(v_val_1297_, 0);
lean_inc(v_pre_1298_);
if (lean_obj_tag(v_pre_1298_) == 1)
{
lean_object* v_pre_1299_; 
v_pre_1299_ = lean_ctor_get(v_pre_1298_, 0);
lean_inc(v_pre_1299_);
if (lean_obj_tag(v_pre_1299_) == 1)
{
lean_object* v_pre_1300_; 
v_pre_1300_ = lean_ctor_get(v_pre_1299_, 0);
if (lean_obj_tag(v_pre_1300_) == 0)
{
lean_object* v_str_1301_; lean_object* v_str_1302_; lean_object* v_str_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_str_1301_ = lean_ctor_get(v_val_1297_, 1);
lean_inc_ref(v_str_1301_);
lean_dec_ref_known(v_val_1297_, 2);
v_str_1302_ = lean_ctor_get(v_pre_1298_, 1);
lean_inc_ref(v_str_1302_);
lean_dec_ref_known(v_pre_1298_, 2);
v_str_1303_ = lean_ctor_get(v_pre_1299_, 1);
lean_inc_ref(v_str_1303_);
lean_dec_ref_known(v_pre_1299_, 2);
v___x_1304_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0));
v___x_1305_ = lean_string_dec_eq(v_str_1303_, v___x_1304_);
lean_dec_ref(v_str_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec_ref(v_str_1302_);
lean_dec_ref(v_str_1301_);
lean_del_object(v___x_1294_);
v___x_1306_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0));
v___x_1308_ = lean_string_dec_eq(v_str_1302_, v___x_1307_);
lean_dec_ref(v_str_1302_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec_ref(v_str_1301_);
lean_del_object(v___x_1294_);
v___x_1309_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1));
v___x_1311_ = lean_string_dec_eq(v_str_1301_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2));
v___x_1313_ = lean_string_dec_eq(v_str_1301_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3));
v___x_1315_ = lean_string_dec_eq(v_str_1301_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4));
v___x_1317_ = lean_string_dec_eq(v_str_1301_, v___x_1316_);
lean_dec_ref(v_str_1301_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_del_object(v___x_1294_);
v___x_1318_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1318_;
}
else
{
uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec_ref(v_e_1285_);
v___x_1319_ = 3;
v___x_1320_ = lean_box(v___x_1319_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1320_);
v___x_1322_ = v___x_1294_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_dec_ref(v_str_1301_);
lean_dec_ref(v_e_1285_);
v___x_1324_ = 2;
v___x_1325_ = lean_box(v___x_1324_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1325_);
v___x_1327_ = v___x_1294_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_dec_ref(v_str_1301_);
lean_dec_ref(v_e_1285_);
v___x_1329_ = 1;
v___x_1330_ = lean_box(v___x_1329_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1330_);
v___x_1332_ = v___x_1294_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec_ref(v_str_1301_);
lean_dec_ref(v_e_1285_);
v___x_1334_ = 0;
v___x_1335_ = lean_box(v___x_1334_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1335_);
v___x_1337_ = v___x_1294_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v_pre_1299_, 2);
lean_dec_ref_known(v_pre_1298_, 2);
lean_dec_ref_known(v_val_1297_, 2);
lean_del_object(v___x_1294_);
v___x_1339_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1339_;
}
}
else
{
lean_object* v___x_1340_; 
lean_dec(v_pre_1299_);
lean_dec_ref_known(v_pre_1298_, 2);
lean_dec_ref_known(v_val_1297_, 2);
lean_del_object(v___x_1294_);
v___x_1340_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1340_;
}
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref_known(v_val_1297_, 2);
lean_dec(v_pre_1298_);
lean_del_object(v___x_1294_);
v___x_1341_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1341_;
}
}
else
{
lean_object* v___x_1342_; 
lean_dec(v_val_1297_);
lean_del_object(v___x_1294_);
v___x_1342_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; 
lean_dec(v___x_1296_);
lean_del_object(v___x_1294_);
v___x_1343_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_e_1285_);
v_a_1345_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1291_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1291_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalBinderInfo___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1285_ = stack[0].m_obj;
lean_object* v_a_1286_ = stack[1].m_obj;
lean_object* v_a_1287_ = stack[2].m_obj;
lean_object* v_a_1288_ = stack[3].m_obj;
lean_object* v_a_1289_ = stack[4].m_obj;
lean_object* v_res_1353_;
v_res_1353_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
stack->m_obj
 = v_res_1353_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(v_e_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
return v_res_1360_;
}
}
lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1(lean_object* v_e_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; 
v___f_1380_ = ((lean_object*)(l_Lean_Meta_instReduceEvalString___closed__0));
v___f_1381_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
lean_inc(v_a_1378_);
lean_inc_ref(v_a_1377_);
lean_inc(v_a_1376_);
lean_inc_ref(v_a_1375_);
v___x_1382_ = lean_whnf(v_e_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2));
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = l_Lean_Expr_isAppOfArity(v_a_1383_, v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4));
v___x_1388_ = l_Lean_Expr_isAppOfArity(v_a_1383_, v___x_1387_, v___x_1385_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1383_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1390_ = l_Lean_Expr_getAppNumArgs(v_a_1383_);
v___x_1391_ = lean_nat_sub(v___x_1390_, v___x_1385_);
lean_dec(v___x_1390_);
v___x_1392_ = l_Lean_Expr_getRevArg_x21(v_a_1383_, v___x_1391_);
lean_dec(v_a_1383_);
v___x_1393_ = l_Lean_Meta_reduceEval___redArg(v___f_1380_, v___x_1392_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1402_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1402_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1402_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_a_1394_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1398_);
v___x_1400_ = v___x_1396_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1393_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1393_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1411_ = l_Lean_Expr_getAppNumArgs(v_a_1383_);
v___x_1412_ = lean_nat_sub(v___x_1411_, v___x_1385_);
lean_dec(v___x_1411_);
v___x_1413_ = l_Lean_Expr_getRevArg_x21(v_a_1383_, v___x_1412_);
lean_dec(v_a_1383_);
v___x_1414_ = l_Lean_Meta_reduceEval___redArg(v___f_1381_, v___x_1413_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_a_1424_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1414_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1414_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1382_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1382_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalLiteral___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1374_ = stack[0].m_obj;
lean_object* v_a_1375_ = stack[1].m_obj;
lean_object* v_a_1376_ = stack[2].m_obj;
lean_object* v_a_1377_ = stack[3].m_obj;
lean_object* v_a_1378_ = stack[4].m_obj;
lean_object* v_res_1440_;
v_res_1440_ = l_Lean_Meta_instReduceEvalLiteral___private__1(v_e_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
stack->m_obj
 = v_res_1440_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(lean_object* v_e_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Meta_instReduceEvalLiteral___private__1(v_e_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1447_;
}
}
lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
lean_inc(v_a_1459_);
lean_inc_ref(v_a_1458_);
lean_inc(v_a_1457_);
lean_inc_ref(v_a_1456_);
v___x_1462_ = lean_whnf(v_e_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = l_Lean_Expr_isAppOfArity(v_a_1463_, v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1463_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1468_ = l_Lean_Expr_getAppNumArgs(v_a_1463_);
v___x_1469_ = lean_nat_sub(v___x_1468_, v___x_1465_);
lean_dec(v___x_1468_);
v___x_1470_ = l_Lean_Expr_getRevArg_x21(v_a_1463_, v___x_1469_);
lean_dec(v_a_1463_);
v___x_1471_ = l_Lean_Meta_reduceEval___redArg(v___x_1461_, v___x_1470_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1471_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1471_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_a_1488_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1462_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1462_);
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
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalMVarId___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1455_ = stack[0].m_obj;
lean_object* v_a_1456_ = stack[1].m_obj;
lean_object* v_a_1457_ = stack[2].m_obj;
lean_object* v_a_1458_ = stack[3].m_obj;
lean_object* v_a_1459_ = stack[4].m_obj;
lean_object* v_res_1496_;
v_res_1496_ = l_Lean_Meta_instReduceEvalMVarId___private__1(v_e_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
stack->m_obj
 = v_res_1496_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object* v_e_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Meta_instReduceEvalMVarId___private__1(v_e_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1503_;
}
}
lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0(lean_object* v_e_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
v___x_1511_ = lean_whnf(v_e_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = l_Lean_Expr_isAppOfArity(v_a_1512_, v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1512_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = l_Lean_Expr_getAppNumArgs(v_a_1512_);
v___x_1518_ = lean_nat_sub(v___x_1517_, v___x_1514_);
lean_dec(v___x_1517_);
v___x_1519_ = l_Lean_Expr_getRevArg_x21(v_a_1512_, v___x_1518_);
lean_dec(v_a_1512_);
v___x_1520_ = l_Lean_Meta_reduceEval___redArg(v___x_1510_, v___x_1519_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1520_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1520_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1511_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1511_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
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
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalMVarId___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1504_ = stack[0].m_obj;
lean_object* v___y_1505_ = stack[1].m_obj;
lean_object* v___y_1506_ = stack[2].m_obj;
lean_object* v___y_1507_ = stack[3].m_obj;
lean_object* v___y_1508_ = stack[4].m_obj;
lean_object* v_res_1545_;
v_res_1545_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(v_e_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
stack->m_obj
 = v_res_1545_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed(lean_object* v_e_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(v_e_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1552_;
}
}
lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1(lean_object* v_e_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
v___x_1567_ = lean_whnf(v_e_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = l_Lean_Expr_isAppOfArity(v_a_1568_, v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1568_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = l_Lean_Expr_getAppNumArgs(v_a_1568_);
v___x_1574_ = lean_nat_sub(v___x_1573_, v___x_1570_);
lean_dec(v___x_1573_);
v___x_1575_ = l_Lean_Expr_getRevArg_x21(v_a_1568_, v___x_1574_);
lean_dec(v_a_1568_);
v___x_1576_ = l_Lean_Meta_reduceEval___redArg(v___x_1566_, v___x_1575_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1576_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1576_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1567_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1567_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalLevelMVarId___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1560_ = stack[0].m_obj;
lean_object* v_a_1561_ = stack[1].m_obj;
lean_object* v_a_1562_ = stack[2].m_obj;
lean_object* v_a_1563_ = stack[3].m_obj;
lean_object* v_a_1564_ = stack[4].m_obj;
lean_object* v_res_1601_;
v_res_1601_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(v_e_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
stack->m_obj
 = v_res_1601_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(lean_object* v_e_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(v_e_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
return v_res_1608_;
}
}
lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(lean_object* v_e_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
v___x_1616_ = lean_whnf(v_e_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = l_Lean_Expr_isAppOfArity(v_a_1617_, v___x_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1617_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1622_ = l_Lean_Expr_getAppNumArgs(v_a_1617_);
v___x_1623_ = lean_nat_sub(v___x_1622_, v___x_1619_);
lean_dec(v___x_1622_);
v___x_1624_ = l_Lean_Expr_getRevArg_x21(v_a_1617_, v___x_1623_);
lean_dec(v_a_1617_);
v___x_1625_ = l_Lean_Meta_reduceEval___redArg(v___x_1615_, v___x_1624_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1625_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1625_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1616_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1616_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalLevelMVarId___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1609_ = stack[0].m_obj;
lean_object* v___y_1610_ = stack[1].m_obj;
lean_object* v___y_1611_ = stack[2].m_obj;
lean_object* v___y_1612_ = stack[3].m_obj;
lean_object* v___y_1613_ = stack[4].m_obj;
lean_object* v_res_1650_;
v_res_1650_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(v_e_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
stack->m_obj
 = v_res_1650_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed(lean_object* v_e_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(v_e_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1657_;
}
}
lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1(lean_object* v_e_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
lean_inc(v_a_1669_);
lean_inc_ref(v_a_1668_);
lean_inc(v_a_1667_);
lean_inc_ref(v_a_1666_);
v___x_1672_ = lean_whnf(v_e_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = l_Lean_Expr_isAppOfArity(v_a_1673_, v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1673_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1678_ = l_Lean_Expr_getAppNumArgs(v_a_1673_);
v___x_1679_ = lean_nat_sub(v___x_1678_, v___x_1675_);
lean_dec(v___x_1678_);
v___x_1680_ = l_Lean_Expr_getRevArg_x21(v_a_1673_, v___x_1679_);
lean_dec(v_a_1673_);
v___x_1681_ = l_Lean_Meta_reduceEval___redArg(v___x_1671_, v___x_1680_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1681_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1681_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1672_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1672_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalFVarId___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1665_ = stack[0].m_obj;
lean_object* v_a_1666_ = stack[1].m_obj;
lean_object* v_a_1667_ = stack[2].m_obj;
lean_object* v_a_1668_ = stack[3].m_obj;
lean_object* v_a_1669_ = stack[4].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l_Lean_Meta_instReduceEvalFVarId___private__1(v_e_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_instReduceEvalFVarId___private__1(v_e_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1713_;
}
}
lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0(lean_object* v_e_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
v___x_1721_ = lean_whnf(v_e_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = l_Lean_Expr_isAppOfArity(v_a_1722_, v___x_1723_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1722_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1727_ = l_Lean_Expr_getAppNumArgs(v_a_1722_);
v___x_1728_ = lean_nat_sub(v___x_1727_, v___x_1724_);
lean_dec(v___x_1727_);
v___x_1729_ = l_Lean_Expr_getRevArg_x21(v_a_1722_, v___x_1728_);
lean_dec(v_a_1722_);
v___x_1730_ = l_Lean_Meta_reduceEval___redArg(v___x_1720_, v___x_1729_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1730_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1730_);
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
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1721_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1721_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReduceEvalFVarId___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1714_ = stack[0].m_obj;
lean_object* v___y_1715_ = stack[1].m_obj;
lean_object* v___y_1716_ = stack[2].m_obj;
lean_object* v___y_1717_ = stack[3].m_obj;
lean_object* v___y_1718_ = stack[4].m_obj;
lean_object* v_res_1755_;
v_res_1755_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(v_e_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
stack->m_obj
 = v_res_1755_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed(lean_object* v_e_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(v_e_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1762_;
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
