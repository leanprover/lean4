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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_instReduceEvalNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalNat___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Meta_instReduceEvalString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalString___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalBitVec___private__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalBitVec___private__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "MVarId"};
static const lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 186, 234, 138, 172, 166, 87, 74)}};
static const lean_ctor_object l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 44, 60, 136, 72, 250, 230, 141)}};
static const lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1 = (const lean_object*)&l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReduceEvalMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalMVarId___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Meta_instReduceEvalFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReduceEvalFVarId___private__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReduceEvalFVarId___closed__0 = (const lean_object*)&l_Lean_Meta_instReduceEvalFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReduceEvalFVarId = (const lean_object*)&l_Lean_Meta_instReduceEvalFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg(lean_object* v_inst_1_, lean_object* v_e_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
uint8_t v___y_9_; lean_object* v___x_68_; uint8_t v_transparency_69_; uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_68_ = l_Lean_Meta_Context_config(v_a_3_);
v_transparency_69_ = lean_ctor_get_uint8(v___x_68_, 9);
lean_dec_ref(v___x_68_);
v___x_70_ = 1;
v___x_71_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_69_, v___x_70_);
if (v___x_71_ == 0)
{
v___y_9_ = v_transparency_69_;
goto v___jp_8_;
}
else
{
v___y_9_ = v___x_70_;
goto v___jp_8_;
}
v___jp_8_:
{
lean_object* v___x_10_; uint8_t v_foApprox_11_; uint8_t v_ctxApprox_12_; uint8_t v_quasiPatternApprox_13_; uint8_t v_constApprox_14_; uint8_t v_isDefEqStuckEx_15_; uint8_t v_unificationHints_16_; uint8_t v_proofIrrelevance_17_; uint8_t v_assignSyntheticOpaque_18_; uint8_t v_offsetCnstrs_19_; uint8_t v_etaStruct_20_; uint8_t v_univApprox_21_; uint8_t v_iota_22_; uint8_t v_beta_23_; uint8_t v_proj_24_; uint8_t v_zeta_25_; uint8_t v_zetaDelta_26_; uint8_t v_zetaUnused_27_; uint8_t v_zetaHave_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_67_; 
v___x_10_ = l_Lean_Meta_Context_config(v_a_3_);
v_foApprox_11_ = lean_ctor_get_uint8(v___x_10_, 0);
v_ctxApprox_12_ = lean_ctor_get_uint8(v___x_10_, 1);
v_quasiPatternApprox_13_ = lean_ctor_get_uint8(v___x_10_, 2);
v_constApprox_14_ = lean_ctor_get_uint8(v___x_10_, 3);
v_isDefEqStuckEx_15_ = lean_ctor_get_uint8(v___x_10_, 4);
v_unificationHints_16_ = lean_ctor_get_uint8(v___x_10_, 5);
v_proofIrrelevance_17_ = lean_ctor_get_uint8(v___x_10_, 6);
v_assignSyntheticOpaque_18_ = lean_ctor_get_uint8(v___x_10_, 7);
v_offsetCnstrs_19_ = lean_ctor_get_uint8(v___x_10_, 8);
v_etaStruct_20_ = lean_ctor_get_uint8(v___x_10_, 10);
v_univApprox_21_ = lean_ctor_get_uint8(v___x_10_, 11);
v_iota_22_ = lean_ctor_get_uint8(v___x_10_, 12);
v_beta_23_ = lean_ctor_get_uint8(v___x_10_, 13);
v_proj_24_ = lean_ctor_get_uint8(v___x_10_, 14);
v_zeta_25_ = lean_ctor_get_uint8(v___x_10_, 15);
v_zetaDelta_26_ = lean_ctor_get_uint8(v___x_10_, 16);
v_zetaUnused_27_ = lean_ctor_get_uint8(v___x_10_, 17);
v_zetaHave_28_ = lean_ctor_get_uint8(v___x_10_, 18);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_67_ == 0)
{
v___x_30_ = v___x_10_;
v_isShared_31_ = v_isSharedCheck_67_;
goto v_resetjp_29_;
}
else
{
lean_dec(v___x_10_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_67_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v_trackZetaDelta_32_; lean_object* v_zetaDeltaSet_33_; lean_object* v_lctx_34_; lean_object* v_localInstances_35_; lean_object* v_defEqCtx_x3f_36_; lean_object* v_synthPendingDepth_37_; lean_object* v_canUnfold_x3f_38_; uint8_t v_univApprox_39_; uint8_t v_inTypeClassResolution_40_; uint8_t v_cacheInferType_41_; lean_object* v_config_43_; 
v_trackZetaDelta_32_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7);
v_zetaDeltaSet_33_ = lean_ctor_get(v_a_3_, 1);
lean_inc(v_zetaDeltaSet_33_);
v_lctx_34_ = lean_ctor_get(v_a_3_, 2);
lean_inc_ref(v_lctx_34_);
v_localInstances_35_ = lean_ctor_get(v_a_3_, 3);
lean_inc_ref(v_localInstances_35_);
v_defEqCtx_x3f_36_ = lean_ctor_get(v_a_3_, 4);
lean_inc(v_defEqCtx_x3f_36_);
v_synthPendingDepth_37_ = lean_ctor_get(v_a_3_, 5);
lean_inc(v_synthPendingDepth_37_);
v_canUnfold_x3f_38_ = lean_ctor_get(v_a_3_, 6);
lean_inc(v_canUnfold_x3f_38_);
v_univApprox_39_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_40_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 2);
v_cacheInferType_41_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7 + 3);
if (v_isShared_31_ == 0)
{
v_config_43_ = v___x_30_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 0, v_foApprox_11_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 1, v_ctxApprox_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 2, v_quasiPatternApprox_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 3, v_constApprox_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 4, v_isDefEqStuckEx_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 5, v_unificationHints_16_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 6, v_proofIrrelevance_17_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 7, v_assignSyntheticOpaque_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 8, v_offsetCnstrs_19_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 10, v_etaStruct_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 11, v_univApprox_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 12, v_iota_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 13, v_beta_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 14, v_proj_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 15, v_zeta_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 16, v_zetaDelta_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 17, v_zetaUnused_27_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 18, v_zetaHave_28_);
v_config_43_ = v_reuseFailAlloc_66_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
uint64_t v___x_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_58_; 
lean_ctor_set_uint8(v_config_43_, 9, v___y_9_);
v___x_44_ = l_Lean_Meta_Context_configKey(v_a_3_);
v_isSharedCheck_58_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; lean_object* v_unused_60_; lean_object* v_unused_61_; lean_object* v_unused_62_; lean_object* v_unused_63_; lean_object* v_unused_64_; lean_object* v_unused_65_; 
v_unused_59_ = lean_ctor_get(v_a_3_, 6);
lean_dec(v_unused_59_);
v_unused_60_ = lean_ctor_get(v_a_3_, 5);
lean_dec(v_unused_60_);
v_unused_61_ = lean_ctor_get(v_a_3_, 4);
lean_dec(v_unused_61_);
v_unused_62_ = lean_ctor_get(v_a_3_, 3);
lean_dec(v_unused_62_);
v_unused_63_ = lean_ctor_get(v_a_3_, 2);
lean_dec(v_unused_63_);
v_unused_64_ = lean_ctor_get(v_a_3_, 1);
lean_dec(v_unused_64_);
v_unused_65_ = lean_ctor_get(v_a_3_, 0);
lean_dec(v_unused_65_);
v___x_46_ = v_a_3_;
v_isShared_47_ = v_isSharedCheck_58_;
goto v_resetjp_45_;
}
else
{
lean_dec(v_a_3_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_58_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
uint64_t v___x_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v_key_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_48_ = 2ULL;
v___x_49_ = lean_uint64_shift_right(v___x_44_, v___x_48_);
v___x_50_ = lean_uint64_shift_left(v___x_49_, v___x_48_);
v___x_51_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_9_);
v_key_52_ = lean_uint64_lor(v___x_50_, v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_53_, 0, v_config_43_);
lean_ctor_set_uint64(v___x_53_, sizeof(void*)*1, v_key_52_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_53_);
v___x_55_ = v___x_46_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v_zetaDeltaSet_33_);
lean_ctor_set(v_reuseFailAlloc_57_, 2, v_lctx_34_);
lean_ctor_set(v_reuseFailAlloc_57_, 3, v_localInstances_35_);
lean_ctor_set(v_reuseFailAlloc_57_, 4, v_defEqCtx_x3f_36_);
lean_ctor_set(v_reuseFailAlloc_57_, 5, v_synthPendingDepth_37_);
lean_ctor_set(v_reuseFailAlloc_57_, 6, v_canUnfold_x3f_38_);
lean_ctor_set_uint8(v_reuseFailAlloc_57_, sizeof(void*)*7, v_trackZetaDelta_32_);
lean_ctor_set_uint8(v_reuseFailAlloc_57_, sizeof(void*)*7 + 1, v_univApprox_39_);
lean_ctor_set_uint8(v_reuseFailAlloc_57_, sizeof(void*)*7 + 2, v_inTypeClassResolution_40_);
lean_ctor_set_uint8(v_reuseFailAlloc_57_, sizeof(void*)*7 + 3, v_cacheInferType_41_);
v___x_55_ = v_reuseFailAlloc_57_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; 
v___x_56_ = lean_apply_6(v_inst_1_, v_e_2_, v___x_55_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
return v___x_56_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object* v_inst_72_, lean_object* v_e_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Meta_reduceEval___redArg(v_inst_72_, v_e_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object* v_00_u03b1_80_, lean_object* v_inst_81_, lean_object* v_e_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_reduceEval___redArg(v_inst_81_, v_e_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object* v_00_u03b1_89_, lean_object* v_inst_90_, lean_object* v_e_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_reduceEval(v_00_u03b1_89_, v_inst_90_, v_e_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(lean_object* v_msgData_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_env_105_; lean_object* v___x_106_; lean_object* v_mctx_107_; lean_object* v_lctx_108_; lean_object* v_options_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_104_ = lean_st_ref_get(v___y_102_);
v_env_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_env_105_);
lean_dec(v___x_104_);
v___x_106_ = lean_st_ref_get(v___y_100_);
v_mctx_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_mctx_107_);
lean_dec(v___x_106_);
v_lctx_108_ = lean_ctor_get(v___y_99_, 2);
v_options_109_ = lean_ctor_get(v___y_101_, 2);
lean_inc_ref(v_options_109_);
lean_inc_ref(v_lctx_108_);
v___x_110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_110_, 0, v_env_105_);
lean_ctor_set(v___x_110_, 1, v_mctx_107_);
lean_ctor_set(v___x_110_, 2, v_lctx_108_);
lean_ctor_set(v___x_110_, 3, v_options_109_);
v___x_111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_msgData_98_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(lean_object* v_msgData_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_ref_126_; lean_object* v___x_127_; lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_ref_126_ = lean_ctor_get(v___y_123_, 5);
v___x_127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
v_a_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc(v_ref_126_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_ref_126_);
lean_ctor_set(v___x_132_, 1, v_a_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 1);
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0));
v___x_146_ = l_Lean_stringToMessageData(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object* v_e_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_153_ = lean_obj_once(&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1, &l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once, _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
v___x_154_ = l_Lean_indentExpr(v_e_147_);
v___x_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_155_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object* v_e_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* v_00_u03b1_164_, lean_object* v_e_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* v_00_u03b1_172_, lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(v_00_u03b1_172_, v_e_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_object* v_00_u03b1_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_188_, v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1(lean_object* v_e_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
lean_inc(v_a_200_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_198_);
lean_inc_ref(v_a_197_);
v___x_202_ = lean_whnf(v_e_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_204_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref(v___x_202_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_203_);
v___x_204_ = l_Lean_Meta_evalNat(v_a_203_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_214_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_214_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
if (lean_obj_tag(v_a_205_) == 1)
{
lean_object* v_val_209_; lean_object* v___x_211_; 
lean_dec(v_a_203_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
v_val_209_ = lean_ctor_get(v_a_205_, 0);
lean_inc(v_val_209_);
lean_dec_ref(v_a_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v_val_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_val_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v___x_213_; 
lean_del_object(v___x_207_);
lean_dec(v_a_205_);
v___x_213_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_203_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v___x_213_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_a_203_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
v_a_215_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_204_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_204_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
v_a_223_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_202_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_202_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1___boxed(lean_object* v_e_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg(lean_object* v_inst_249_, lean_object* v_e_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; 
lean_inc(v_a_254_);
lean_inc_ref(v_a_253_);
lean_inc(v_a_252_);
lean_inc_ref(v_a_251_);
v___x_256_ = lean_whnf(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_301_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_301_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___y_262_; lean_object* v___x_283_; 
v___x_283_ = l_Lean_Expr_getAppFn(v_a_257_);
if (lean_obj_tag(v___x_283_) == 4)
{
lean_object* v_declName_284_; lean_object* v___x_285_; uint8_t v___y_287_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_declName_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_declName_284_);
lean_dec_ref(v___x_283_);
v___x_285_ = l_Lean_Expr_getAppNumArgs(v_a_257_);
v___x_296_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_297_ = lean_name_eq(v_declName_284_, v___x_296_);
if (v___x_297_ == 0)
{
v___y_287_ = v___x_297_;
goto v___jp_286_;
}
else
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v___x_285_, v___x_298_);
v___y_287_ = v___x_299_;
goto v___jp_286_;
}
v___jp_286_:
{
if (v___y_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
lean_del_object(v___x_259_);
v___x_288_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_289_ = lean_name_eq(v_declName_284_, v___x_288_);
lean_dec(v_declName_284_);
if (v___x_289_ == 0)
{
lean_dec(v___x_285_);
v___y_262_ = v___x_289_;
goto v___jp_261_;
}
else
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_dec_eq(v___x_285_, v___x_290_);
lean_dec(v___x_285_);
v___y_262_ = v___x_291_;
goto v___jp_261_;
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v___x_285_);
lean_dec(v_declName_284_);
lean_dec(v_a_257_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_inst_249_);
v___x_292_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_292_);
v___x_294_ = v___x_259_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_259_);
lean_dec_ref(v_inst_249_);
v___x_300_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_257_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v___x_300_;
}
v___jp_261_:
{
if (v___y_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec_ref(v_inst_249_);
v___x_263_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_257_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = l_Lean_Expr_appArg_x21(v_a_257_);
lean_dec(v_a_257_);
v___x_265_ = l_Lean_Meta_reduceEval___redArg(v_inst_249_, v___x_264_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_a_266_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_265_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_265_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_inst_249_);
v_a_302_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_256_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_256_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(lean_object* v_inst_310_, lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_310_, v_e_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1(lean_object* v_00_u03b1_318_, lean_object* v_inst_319_, lean_object* v_e_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_319_, v_e_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___boxed(lean_object* v_00_u03b1_327_, lean_object* v_inst_328_, lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_instReduceEvalOption___private__1(v_00_u03b1_327_, v_inst_328_, v_e_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object* v_inst_336_, lean_object* v_e_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_336_, v_e_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(lean_object* v_inst_344_, lean_object* v_e_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(v_inst_344_, v_e_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object* v_inst_352_){
_start:
{
lean_object* v___f_353_; 
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_353_, 0, v_inst_352_);
return v___f_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* v_00_u03b1_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v___f_356_; 
v___f_356_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_356_, 0, v_inst_355_);
return v___f_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1(lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
lean_inc(v_a_361_);
lean_inc_ref(v_a_360_);
lean_inc(v_a_359_);
lean_inc_ref(v_a_358_);
lean_inc_ref(v_e_357_);
v___x_363_ = lean_whnf(v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_375_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_375_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
if (lean_obj_tag(v_a_364_) == 9)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v_a_364_, 0);
lean_inc_ref(v_a_368_);
lean_dec_ref(v_a_364_);
if (lean_obj_tag(v_a_368_) == 1)
{
lean_object* v_val_369_; lean_object* v___x_371_; 
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_e_357_);
v_val_369_ = lean_ctor_get(v_a_368_, 0);
lean_inc_ref(v_val_369_);
lean_dec_ref(v_a_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v_val_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_val_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v___x_373_; 
lean_dec_ref(v_a_368_);
lean_del_object(v___x_366_);
v___x_373_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v___x_373_;
}
}
else
{
lean_object* v___x_374_; 
lean_del_object(v___x_366_);
lean_dec(v_a_364_);
v___x_374_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v___x_374_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_e_357_);
v_a_376_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_363_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_363_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1___boxed(lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
uint8_t v___y_400_; lean_object* v___x_459_; uint8_t v_transparency_460_; uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_459_ = l_Lean_Meta_Context_config(v_a_394_);
v_transparency_460_ = lean_ctor_get_uint8(v___x_459_, 9);
lean_dec_ref(v___x_459_);
v___x_461_ = 1;
v___x_462_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_460_, v___x_461_);
if (v___x_462_ == 0)
{
v___y_400_ = v_transparency_460_;
goto v___jp_399_;
}
else
{
v___y_400_ = v___x_461_;
goto v___jp_399_;
}
v___jp_399_:
{
lean_object* v___x_401_; uint8_t v_foApprox_402_; uint8_t v_ctxApprox_403_; uint8_t v_quasiPatternApprox_404_; uint8_t v_constApprox_405_; uint8_t v_isDefEqStuckEx_406_; uint8_t v_unificationHints_407_; uint8_t v_proofIrrelevance_408_; uint8_t v_assignSyntheticOpaque_409_; uint8_t v_offsetCnstrs_410_; uint8_t v_etaStruct_411_; uint8_t v_univApprox_412_; uint8_t v_iota_413_; uint8_t v_beta_414_; uint8_t v_proj_415_; uint8_t v_zeta_416_; uint8_t v_zetaDelta_417_; uint8_t v_zetaUnused_418_; uint8_t v_zetaHave_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_458_; 
v___x_401_ = l_Lean_Meta_Context_config(v_a_394_);
v_foApprox_402_ = lean_ctor_get_uint8(v___x_401_, 0);
v_ctxApprox_403_ = lean_ctor_get_uint8(v___x_401_, 1);
v_quasiPatternApprox_404_ = lean_ctor_get_uint8(v___x_401_, 2);
v_constApprox_405_ = lean_ctor_get_uint8(v___x_401_, 3);
v_isDefEqStuckEx_406_ = lean_ctor_get_uint8(v___x_401_, 4);
v_unificationHints_407_ = lean_ctor_get_uint8(v___x_401_, 5);
v_proofIrrelevance_408_ = lean_ctor_get_uint8(v___x_401_, 6);
v_assignSyntheticOpaque_409_ = lean_ctor_get_uint8(v___x_401_, 7);
v_offsetCnstrs_410_ = lean_ctor_get_uint8(v___x_401_, 8);
v_etaStruct_411_ = lean_ctor_get_uint8(v___x_401_, 10);
v_univApprox_412_ = lean_ctor_get_uint8(v___x_401_, 11);
v_iota_413_ = lean_ctor_get_uint8(v___x_401_, 12);
v_beta_414_ = lean_ctor_get_uint8(v___x_401_, 13);
v_proj_415_ = lean_ctor_get_uint8(v___x_401_, 14);
v_zeta_416_ = lean_ctor_get_uint8(v___x_401_, 15);
v_zetaDelta_417_ = lean_ctor_get_uint8(v___x_401_, 16);
v_zetaUnused_418_ = lean_ctor_get_uint8(v___x_401_, 17);
v_zetaHave_419_ = lean_ctor_get_uint8(v___x_401_, 18);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_458_ == 0)
{
v___x_421_ = v___x_401_;
v_isShared_422_ = v_isSharedCheck_458_;
goto v_resetjp_420_;
}
else
{
lean_dec(v___x_401_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_458_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint8_t v_trackZetaDelta_423_; lean_object* v_zetaDeltaSet_424_; lean_object* v_lctx_425_; lean_object* v_localInstances_426_; lean_object* v_defEqCtx_x3f_427_; lean_object* v_synthPendingDepth_428_; lean_object* v_canUnfold_x3f_429_; uint8_t v_univApprox_430_; uint8_t v_inTypeClassResolution_431_; uint8_t v_cacheInferType_432_; lean_object* v_config_434_; 
v_trackZetaDelta_423_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7);
v_zetaDeltaSet_424_ = lean_ctor_get(v_a_394_, 1);
lean_inc(v_zetaDeltaSet_424_);
v_lctx_425_ = lean_ctor_get(v_a_394_, 2);
lean_inc_ref(v_lctx_425_);
v_localInstances_426_ = lean_ctor_get(v_a_394_, 3);
lean_inc_ref(v_localInstances_426_);
v_defEqCtx_x3f_427_ = lean_ctor_get(v_a_394_, 4);
lean_inc(v_defEqCtx_x3f_427_);
v_synthPendingDepth_428_ = lean_ctor_get(v_a_394_, 5);
lean_inc(v_synthPendingDepth_428_);
v_canUnfold_x3f_429_ = lean_ctor_get(v_a_394_, 6);
lean_inc(v_canUnfold_x3f_429_);
v_univApprox_430_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_431_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7 + 2);
v_cacheInferType_432_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7 + 3);
if (v_isShared_422_ == 0)
{
v_config_434_ = v___x_421_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 0, v_foApprox_402_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 1, v_ctxApprox_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 2, v_quasiPatternApprox_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 3, v_constApprox_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 4, v_isDefEqStuckEx_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 5, v_unificationHints_407_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 6, v_proofIrrelevance_408_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 7, v_assignSyntheticOpaque_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 8, v_offsetCnstrs_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 10, v_etaStruct_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 11, v_univApprox_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 12, v_iota_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 13, v_beta_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 14, v_proj_415_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 15, v_zeta_416_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 16, v_zetaDelta_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 17, v_zetaUnused_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, 18, v_zetaHave_419_);
v_config_434_ = v_reuseFailAlloc_457_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
uint64_t v___x_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_449_; 
lean_ctor_set_uint8(v_config_434_, 9, v___y_400_);
v___x_435_ = l_Lean_Meta_Context_configKey(v_a_394_);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_394_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; 
v_unused_450_ = lean_ctor_get(v_a_394_, 6);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_a_394_, 5);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_a_394_, 4);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_a_394_, 3);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_a_394_, 2);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_a_394_, 1);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_a_394_, 0);
lean_dec(v_unused_456_);
v___x_437_ = v_a_394_;
v_isShared_438_ = v_isSharedCheck_449_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_a_394_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_449_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v_key_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_439_ = 2ULL;
v___x_440_ = lean_uint64_shift_right(v___x_435_, v___x_439_);
v___x_441_ = lean_uint64_shift_left(v___x_440_, v___x_439_);
v___x_442_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_400_);
v_key_443_ = lean_uint64_lor(v___x_441_, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_444_, 0, v_config_434_);
lean_ctor_set_uint64(v___x_444_, sizeof(void*)*1, v_key_443_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_444_);
v___x_446_ = v___x_437_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_zetaDeltaSet_424_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_lctx_425_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_localInstances_426_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_defEqCtx_x3f_427_);
lean_ctor_set(v_reuseFailAlloc_448_, 5, v_synthPendingDepth_428_);
lean_ctor_set(v_reuseFailAlloc_448_, 6, v_canUnfold_x3f_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*7, v_trackZetaDelta_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*7 + 1, v_univApprox_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*7 + 2, v_inTypeClassResolution_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*7 + 3, v_cacheInferType_432_);
v___x_446_ = v_reuseFailAlloc_448_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_393_, v___x_446_, v_a_395_, v_a_396_, v_a_397_);
return v___x_447_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object* v_e_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
uint8_t v___y_477_; lean_object* v___x_536_; uint8_t v_transparency_537_; uint8_t v___x_538_; uint8_t v___x_539_; 
v___x_536_ = l_Lean_Meta_Context_config(v_a_471_);
v_transparency_537_ = lean_ctor_get_uint8(v___x_536_, 9);
lean_dec_ref(v___x_536_);
v___x_538_ = 1;
v___x_539_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_537_, v___x_538_);
if (v___x_539_ == 0)
{
v___y_477_ = v_transparency_537_;
goto v___jp_476_;
}
else
{
v___y_477_ = v___x_538_;
goto v___jp_476_;
}
v___jp_476_:
{
lean_object* v___x_478_; uint8_t v_foApprox_479_; uint8_t v_ctxApprox_480_; uint8_t v_quasiPatternApprox_481_; uint8_t v_constApprox_482_; uint8_t v_isDefEqStuckEx_483_; uint8_t v_unificationHints_484_; uint8_t v_proofIrrelevance_485_; uint8_t v_assignSyntheticOpaque_486_; uint8_t v_offsetCnstrs_487_; uint8_t v_etaStruct_488_; uint8_t v_univApprox_489_; uint8_t v_iota_490_; uint8_t v_beta_491_; uint8_t v_proj_492_; uint8_t v_zeta_493_; uint8_t v_zetaDelta_494_; uint8_t v_zetaUnused_495_; uint8_t v_zetaHave_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_535_; 
v___x_478_ = l_Lean_Meta_Context_config(v_a_471_);
v_foApprox_479_ = lean_ctor_get_uint8(v___x_478_, 0);
v_ctxApprox_480_ = lean_ctor_get_uint8(v___x_478_, 1);
v_quasiPatternApprox_481_ = lean_ctor_get_uint8(v___x_478_, 2);
v_constApprox_482_ = lean_ctor_get_uint8(v___x_478_, 3);
v_isDefEqStuckEx_483_ = lean_ctor_get_uint8(v___x_478_, 4);
v_unificationHints_484_ = lean_ctor_get_uint8(v___x_478_, 5);
v_proofIrrelevance_485_ = lean_ctor_get_uint8(v___x_478_, 6);
v_assignSyntheticOpaque_486_ = lean_ctor_get_uint8(v___x_478_, 7);
v_offsetCnstrs_487_ = lean_ctor_get_uint8(v___x_478_, 8);
v_etaStruct_488_ = lean_ctor_get_uint8(v___x_478_, 10);
v_univApprox_489_ = lean_ctor_get_uint8(v___x_478_, 11);
v_iota_490_ = lean_ctor_get_uint8(v___x_478_, 12);
v_beta_491_ = lean_ctor_get_uint8(v___x_478_, 13);
v_proj_492_ = lean_ctor_get_uint8(v___x_478_, 14);
v_zeta_493_ = lean_ctor_get_uint8(v___x_478_, 15);
v_zetaDelta_494_ = lean_ctor_get_uint8(v___x_478_, 16);
v_zetaUnused_495_ = lean_ctor_get_uint8(v___x_478_, 17);
v_zetaHave_496_ = lean_ctor_get_uint8(v___x_478_, 18);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_535_ == 0)
{
v___x_498_ = v___x_478_;
v_isShared_499_ = v_isSharedCheck_535_;
goto v_resetjp_497_;
}
else
{
lean_dec(v___x_478_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_535_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
uint8_t v_trackZetaDelta_500_; lean_object* v_zetaDeltaSet_501_; lean_object* v_lctx_502_; lean_object* v_localInstances_503_; lean_object* v_defEqCtx_x3f_504_; lean_object* v_synthPendingDepth_505_; lean_object* v_canUnfold_x3f_506_; uint8_t v_univApprox_507_; uint8_t v_inTypeClassResolution_508_; uint8_t v_cacheInferType_509_; lean_object* v_config_511_; 
v_trackZetaDelta_500_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7);
v_zetaDeltaSet_501_ = lean_ctor_get(v_a_471_, 1);
lean_inc(v_zetaDeltaSet_501_);
v_lctx_502_ = lean_ctor_get(v_a_471_, 2);
lean_inc_ref(v_lctx_502_);
v_localInstances_503_ = lean_ctor_get(v_a_471_, 3);
lean_inc_ref(v_localInstances_503_);
v_defEqCtx_x3f_504_ = lean_ctor_get(v_a_471_, 4);
lean_inc(v_defEqCtx_x3f_504_);
v_synthPendingDepth_505_ = lean_ctor_get(v_a_471_, 5);
lean_inc(v_synthPendingDepth_505_);
v_canUnfold_x3f_506_ = lean_ctor_get(v_a_471_, 6);
lean_inc(v_canUnfold_x3f_506_);
v_univApprox_507_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_508_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7 + 2);
v_cacheInferType_509_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7 + 3);
if (v_isShared_499_ == 0)
{
v_config_511_ = v___x_498_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 0, v_foApprox_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 1, v_ctxApprox_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 2, v_quasiPatternApprox_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 3, v_constApprox_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 4, v_isDefEqStuckEx_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 5, v_unificationHints_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 6, v_proofIrrelevance_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 7, v_assignSyntheticOpaque_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 8, v_offsetCnstrs_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 10, v_etaStruct_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 11, v_univApprox_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 12, v_iota_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 13, v_beta_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 14, v_proj_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 15, v_zeta_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 16, v_zetaDelta_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 17, v_zetaUnused_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_534_, 18, v_zetaHave_496_);
v_config_511_ = v_reuseFailAlloc_534_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
uint64_t v___x_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_526_; 
lean_ctor_set_uint8(v_config_511_, 9, v___y_477_);
v___x_512_ = l_Lean_Meta_Context_configKey(v_a_471_);
v_isSharedCheck_526_ = !lean_is_exclusive(v_a_471_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_527_ = lean_ctor_get(v_a_471_, 6);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_a_471_, 5);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_a_471_, 4);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_a_471_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_a_471_, 2);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_a_471_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_a_471_, 0);
lean_dec(v_unused_533_);
v___x_514_ = v_a_471_;
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
else
{
lean_dec(v_a_471_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v_key_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_516_ = 2ULL;
v___x_517_ = lean_uint64_shift_right(v___x_512_, v___x_516_);
v___x_518_ = lean_uint64_shift_left(v___x_517_, v___x_516_);
v___x_519_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_477_);
v_key_520_ = lean_uint64_lor(v___x_518_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_521_, 0, v_config_511_);
lean_ctor_set_uint64(v___x_521_, sizeof(void*)*1, v_key_520_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_521_);
v___x_523_ = v___x_514_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_zetaDeltaSet_501_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_lctx_502_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_localInstances_503_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_defEqCtx_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_synthPendingDepth_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_canUnfold_x3f_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_525_, sizeof(void*)*7, v_trackZetaDelta_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_525_, sizeof(void*)*7 + 1, v_univApprox_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_525_, sizeof(void*)*7 + 2, v_inTypeClassResolution_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_525_, sizeof(void*)*7 + 3, v_cacheInferType_509_);
v___x_523_ = v_reuseFailAlloc_525_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_470_, v___x_523_, v_a_472_, v_a_473_, v_a_474_);
return v___x_524_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object* v_e_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object* v___x_547_, lean_object* v_00___548_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(2u);
v___x_550_ = lean_nat_dec_eq(v___x_547_, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object* v___x_551_, lean_object* v_00___552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_551_, v_00___552_);
lean_dec(v___x_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_578_ = lean_whnf(v_e_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_660_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_660_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_660_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_660_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Expr_getAppFn(v_a_579_);
if (lean_obj_tag(v___x_583_) == 4)
{
lean_object* v_declName_584_; lean_object* v___x_585_; uint8_t v___y_587_; uint8_t v___y_615_; uint8_t v___y_646_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_declName_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_declName_584_);
lean_dec_ref(v___x_583_);
v___x_585_ = l_Lean_Expr_getAppNumArgs(v_a_579_);
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7));
v___x_656_ = lean_name_eq(v_declName_584_, v___x_655_);
if (v___x_656_ == 0)
{
v___y_646_ = v___x_656_;
goto v___jp_645_;
}
else
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_eq(v___x_585_, v___x_657_);
v___y_646_ = v___x_658_;
goto v___jp_645_;
}
v___jp_586_:
{
if (v___y_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v___x_585_);
v___x_588_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_579_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_sub(v___x_585_, v___x_589_);
lean_dec(v___x_585_);
lean_inc(v___x_590_);
v___x_591_ = l_Lean_Expr_getRevArg_x21(v_a_579_, v___x_590_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_592_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_591_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v___x_594_ = lean_nat_sub(v___x_590_, v___x_589_);
lean_dec(v___x_590_);
v___x_595_ = l_Lean_Expr_getRevArg_x21(v_a_579_, v___x_594_);
lean_dec(v_a_579_);
v___x_596_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_595_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_605_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = l_Lean_Name_num___override(v_a_593_, v_a_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
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
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_593_);
v_a_606_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_596_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_596_);
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
lean_dec(v___x_590_);
lean_dec(v_a_579_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v___x_592_;
}
}
}
v___jp_614_:
{
if (v___y_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3));
v___x_617_ = lean_name_eq(v_declName_584_, v___x_616_);
lean_dec(v_declName_584_);
if (v___x_617_ == 0)
{
v___y_587_ = v___x_617_;
goto v___jp_586_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_box(0);
v___x_619_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_585_, v___x_618_);
v___y_587_ = v___x_619_;
goto v___jp_586_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v_declName_584_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_sub(v___x_585_, v___x_620_);
lean_dec(v___x_585_);
lean_inc(v___x_621_);
v___x_622_ = l_Lean_Expr_getRevArg_x21(v_a_579_, v___x_621_);
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_623_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_622_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_nat_sub(v___x_621_, v___x_620_);
lean_dec(v___x_621_);
v___x_626_ = l_Lean_Expr_getRevArg_x21(v_a_579_, v___x_625_);
lean_dec(v_a_579_);
v___x_627_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_626_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_636_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_636_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_636_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_636_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = l_Lean_Name_str___override(v_a_624_, v_a_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_632_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_a_624_);
v_a_637_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_627_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_627_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
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
lean_dec(v___x_621_);
lean_dec(v_a_579_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v___x_623_;
}
}
}
v___jp_645_:
{
if (v___y_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
lean_del_object(v___x_581_);
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5));
v___x_648_ = lean_name_eq(v_declName_584_, v___x_647_);
if (v___x_648_ == 0)
{
v___y_615_ = v___x_648_;
goto v___jp_614_;
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_585_, v___x_649_);
v___y_615_ = v___x_650_;
goto v___jp_614_;
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_653_; 
lean_dec(v___x_585_);
lean_dec(v_declName_584_);
lean_dec(v_a_579_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
v___x_651_ = lean_box(0);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_651_);
v___x_653_ = v___x_581_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
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
else
{
lean_object* v___x_659_; 
lean_dec_ref(v___x_583_);
lean_del_object(v___x_581_);
v___x_659_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_579_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v___x_659_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
v_a_661_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_578_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_578_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1(lean_object* v_e_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1___boxed(lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_instReduceEvalName___private__1(v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(lean_object* v_inst_695_, lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; 
lean_inc(v_a_700_);
lean_inc_ref(v_a_699_);
lean_inc(v_a_698_);
lean_inc_ref(v_a_697_);
v___x_702_ = lean_whnf(v_e_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_764_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_764_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_764_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_764_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Expr_getAppFn(v_a_703_);
if (lean_obj_tag(v___x_707_) == 4)
{
lean_object* v_declName_708_; 
v_declName_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_declName_708_);
lean_dec_ref(v___x_707_);
if (lean_obj_tag(v_declName_708_) == 1)
{
lean_object* v_pre_709_; 
v_pre_709_ = lean_ctor_get(v_declName_708_, 0);
lean_inc(v_pre_709_);
if (lean_obj_tag(v_pre_709_) == 1)
{
lean_object* v_pre_710_; 
v_pre_710_ = lean_ctor_get(v_pre_709_, 0);
if (lean_obj_tag(v_pre_710_) == 0)
{
lean_object* v_str_711_; lean_object* v_str_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_str_711_ = lean_ctor_get(v_declName_708_, 1);
lean_inc_ref(v_str_711_);
lean_dec_ref(v_declName_708_);
v_str_712_ = lean_ctor_get(v_pre_709_, 1);
lean_inc_ref(v_str_712_);
lean_dec_ref(v_pre_709_);
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0));
v___x_714_ = lean_string_dec_eq(v_str_712_, v___x_713_);
lean_dec_ref(v_str_712_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec_ref(v_str_711_);
lean_del_object(v___x_705_);
lean_dec_ref(v_inst_695_);
v___x_715_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = l_Lean_Expr_getAppNumArgs(v_a_703_);
v___x_717_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1));
v___x_718_ = lean_string_dec_eq(v_str_711_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; uint8_t v___x_720_; 
lean_del_object(v___x_705_);
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2));
v___x_720_ = lean_string_dec_eq(v_str_711_, v___x_719_);
lean_dec_ref(v_str_711_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v___x_716_);
lean_dec_ref(v_inst_695_);
v___x_721_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(3u);
v___x_723_ = lean_nat_dec_eq(v___x_716_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v___x_716_);
lean_dec_ref(v_inst_695_);
v___x_724_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_sub(v___x_716_, v___x_725_);
v___x_727_ = lean_nat_sub(v___x_726_, v___x_725_);
lean_dec(v___x_726_);
v___x_728_ = l_Lean_Expr_getRevArg_x21(v_a_703_, v___x_727_);
lean_inc(v_a_700_);
lean_inc_ref(v_a_699_);
lean_inc(v_a_698_);
lean_inc_ref(v_a_697_);
lean_inc_ref(v_inst_695_);
v___x_729_ = l_Lean_Meta_reduceEval___redArg(v_inst_695_, v___x_728_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_nat_sub(v___x_716_, v___x_731_);
lean_dec(v___x_716_);
v___x_733_ = lean_nat_sub(v___x_732_, v___x_725_);
lean_dec(v___x_732_);
v___x_734_ = l_Lean_Expr_getRevArg_x21(v_a_703_, v___x_733_);
lean_dec(v_a_703_);
v___x_735_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_695_, v___x_734_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_a_730_);
lean_ctor_set(v___x_740_, 1, v_a_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_dec(v_a_730_);
return v___x_735_;
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_716_);
lean_dec(v_a_703_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_inst_695_);
v_a_745_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_729_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_729_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
else
{
lean_object* v___x_753_; uint8_t v___x_754_; 
lean_dec_ref(v_str_711_);
lean_dec_ref(v_inst_695_);
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_dec_eq(v___x_716_, v___x_753_);
lean_dec(v___x_716_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_del_object(v___x_705_);
v___x_755_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec(v_a_703_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
v___x_756_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_756_);
v___x_758_ = v___x_705_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
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
lean_object* v___x_760_; 
lean_dec_ref(v_pre_709_);
lean_dec_ref(v_declName_708_);
lean_del_object(v___x_705_);
lean_dec_ref(v_inst_695_);
v___x_760_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_760_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_pre_709_);
lean_dec_ref(v_declName_708_);
lean_del_object(v___x_705_);
lean_dec_ref(v_inst_695_);
v___x_761_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_761_;
}
}
else
{
lean_object* v___x_762_; 
lean_dec(v_declName_708_);
lean_del_object(v___x_705_);
lean_dec_ref(v_inst_695_);
v___x_762_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_762_;
}
}
else
{
lean_object* v___x_763_; 
lean_dec_ref(v___x_707_);
lean_del_object(v___x_705_);
lean_dec_ref(v_inst_695_);
v___x_763_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v___x_763_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_inst_695_);
v_a_765_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_702_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_702_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(lean_object* v_inst_773_, lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_773_, v_e_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_object* v_00_u03b1_781_, lean_object* v_inst_782_, lean_object* v_e_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_782_, v_e_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(lean_object* v_00_u03b1_790_, lean_object* v_inst_791_, lean_object* v_e_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(v_00_u03b1_790_, v_inst_791_, v_e_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg(lean_object* v_inst_799_, lean_object* v_e_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_799_, v_e_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(lean_object* v_inst_807_, lean_object* v_e_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(v_inst_807_, v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1(lean_object* v_00_u03b1_815_, lean_object* v_inst_816_, lean_object* v_e_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_816_, v_e_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___boxed(lean_object* v_00_u03b1_824_, lean_object* v_inst_825_, lean_object* v_e_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Meta_instReduceEvalList___private__1(v_00_u03b1_824_, v_inst_825_, v_e_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___redArg(lean_object* v_inst_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_834_, 0, lean_box(0));
lean_closure_set(v___x_834_, 1, v_inst_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList(lean_object* v_00_u03b1_835_, lean_object* v_inst_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_837_, 0, lean_box(0));
lean_closure_set(v___x_837_, 1, v_inst_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(lean_object* v_n_843_, lean_object* v_e_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; 
lean_inc(v_a_848_);
lean_inc_ref(v_a_847_);
lean_inc(v_a_846_);
lean_inc_ref(v_a_845_);
v___x_850_ = lean_whnf(v_e_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_853_ = lean_unsigned_to_nat(3u);
v___x_854_ = l_Lean_Expr_isAppOfArity(v_a_851_, v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_851_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v___x_855_;
}
else
{
lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___f_856_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = l_Lean_Expr_getAppNumArgs(v_a_851_);
v___x_859_ = lean_nat_sub(v___x_858_, v___x_857_);
lean_dec(v___x_858_);
v___x_860_ = lean_nat_sub(v___x_859_, v___x_857_);
lean_dec(v___x_859_);
v___x_861_ = l_Lean_Expr_getRevArg_x21(v_a_851_, v___x_860_);
lean_dec(v_a_851_);
v___x_862_ = l_Lean_Meta_reduceEval___redArg(v___f_856_, v___x_861_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_nat_mod(v_a_863_, v_n_843_);
lean_dec(v_a_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
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
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_862_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_862_);
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
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
v_a_880_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_850_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_850_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(lean_object* v_n_888_, lean_object* v_e_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_888_, v_e_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_n_888_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(lean_object* v_n_896_, lean_object* v_inst_897_, lean_object* v_e_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_896_, v_e_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(lean_object* v_n_905_, lean_object* v_inst_906_, lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(v_n_905_, v_inst_906_, v_e_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_n_905_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(lean_object* v_n_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_915_, 0, v_n_914_);
lean_closure_set(v___x_915_, 1, lean_box(0));
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat(lean_object* v_n_916_, lean_object* v_inst_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_918_, 0, v_n_916_);
lean_closure_set(v___x_918_, 1, lean_box(0));
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalBitVec___private__1_spec__0(lean_object* v___x_919_, lean_object* v_e_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint8_t v___y_927_; lean_object* v___x_986_; uint8_t v_transparency_987_; uint8_t v___x_988_; uint8_t v___x_989_; 
v___x_986_ = l_Lean_Meta_Context_config(v_a_921_);
v_transparency_987_ = lean_ctor_get_uint8(v___x_986_, 9);
lean_dec_ref(v___x_986_);
v___x_988_ = 1;
v___x_989_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_987_, v___x_988_);
if (v___x_989_ == 0)
{
v___y_927_ = v_transparency_987_;
goto v___jp_926_;
}
else
{
v___y_927_ = v___x_988_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; uint8_t v_foApprox_929_; uint8_t v_ctxApprox_930_; uint8_t v_quasiPatternApprox_931_; uint8_t v_constApprox_932_; uint8_t v_isDefEqStuckEx_933_; uint8_t v_unificationHints_934_; uint8_t v_proofIrrelevance_935_; uint8_t v_assignSyntheticOpaque_936_; uint8_t v_offsetCnstrs_937_; uint8_t v_etaStruct_938_; uint8_t v_univApprox_939_; uint8_t v_iota_940_; uint8_t v_beta_941_; uint8_t v_proj_942_; uint8_t v_zeta_943_; uint8_t v_zetaDelta_944_; uint8_t v_zetaUnused_945_; uint8_t v_zetaHave_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_985_; 
v___x_928_ = l_Lean_Meta_Context_config(v_a_921_);
v_foApprox_929_ = lean_ctor_get_uint8(v___x_928_, 0);
v_ctxApprox_930_ = lean_ctor_get_uint8(v___x_928_, 1);
v_quasiPatternApprox_931_ = lean_ctor_get_uint8(v___x_928_, 2);
v_constApprox_932_ = lean_ctor_get_uint8(v___x_928_, 3);
v_isDefEqStuckEx_933_ = lean_ctor_get_uint8(v___x_928_, 4);
v_unificationHints_934_ = lean_ctor_get_uint8(v___x_928_, 5);
v_proofIrrelevance_935_ = lean_ctor_get_uint8(v___x_928_, 6);
v_assignSyntheticOpaque_936_ = lean_ctor_get_uint8(v___x_928_, 7);
v_offsetCnstrs_937_ = lean_ctor_get_uint8(v___x_928_, 8);
v_etaStruct_938_ = lean_ctor_get_uint8(v___x_928_, 10);
v_univApprox_939_ = lean_ctor_get_uint8(v___x_928_, 11);
v_iota_940_ = lean_ctor_get_uint8(v___x_928_, 12);
v_beta_941_ = lean_ctor_get_uint8(v___x_928_, 13);
v_proj_942_ = lean_ctor_get_uint8(v___x_928_, 14);
v_zeta_943_ = lean_ctor_get_uint8(v___x_928_, 15);
v_zetaDelta_944_ = lean_ctor_get_uint8(v___x_928_, 16);
v_zetaUnused_945_ = lean_ctor_get_uint8(v___x_928_, 17);
v_zetaHave_946_ = lean_ctor_get_uint8(v___x_928_, 18);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_985_ == 0)
{
v___x_948_ = v___x_928_;
v_isShared_949_ = v_isSharedCheck_985_;
goto v_resetjp_947_;
}
else
{
lean_dec(v___x_928_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_985_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v_trackZetaDelta_950_; lean_object* v_zetaDeltaSet_951_; lean_object* v_lctx_952_; lean_object* v_localInstances_953_; lean_object* v_defEqCtx_x3f_954_; lean_object* v_synthPendingDepth_955_; lean_object* v_canUnfold_x3f_956_; uint8_t v_univApprox_957_; uint8_t v_inTypeClassResolution_958_; uint8_t v_cacheInferType_959_; lean_object* v_config_961_; 
v_trackZetaDelta_950_ = lean_ctor_get_uint8(v_a_921_, sizeof(void*)*7);
v_zetaDeltaSet_951_ = lean_ctor_get(v_a_921_, 1);
lean_inc(v_zetaDeltaSet_951_);
v_lctx_952_ = lean_ctor_get(v_a_921_, 2);
lean_inc_ref(v_lctx_952_);
v_localInstances_953_ = lean_ctor_get(v_a_921_, 3);
lean_inc_ref(v_localInstances_953_);
v_defEqCtx_x3f_954_ = lean_ctor_get(v_a_921_, 4);
lean_inc(v_defEqCtx_x3f_954_);
v_synthPendingDepth_955_ = lean_ctor_get(v_a_921_, 5);
lean_inc(v_synthPendingDepth_955_);
v_canUnfold_x3f_956_ = lean_ctor_get(v_a_921_, 6);
lean_inc(v_canUnfold_x3f_956_);
v_univApprox_957_ = lean_ctor_get_uint8(v_a_921_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_958_ = lean_ctor_get_uint8(v_a_921_, sizeof(void*)*7 + 2);
v_cacheInferType_959_ = lean_ctor_get_uint8(v_a_921_, sizeof(void*)*7 + 3);
if (v_isShared_949_ == 0)
{
v_config_961_ = v___x_948_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 0, v_foApprox_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 1, v_ctxApprox_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 2, v_quasiPatternApprox_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 3, v_constApprox_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 4, v_isDefEqStuckEx_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 5, v_unificationHints_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 6, v_proofIrrelevance_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 7, v_assignSyntheticOpaque_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 8, v_offsetCnstrs_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 10, v_etaStruct_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 11, v_univApprox_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 12, v_iota_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 13, v_beta_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 14, v_proj_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 15, v_zeta_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 16, v_zetaDelta_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 17, v_zetaUnused_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, 18, v_zetaHave_946_);
v_config_961_ = v_reuseFailAlloc_984_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
uint64_t v___x_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_976_; 
lean_ctor_set_uint8(v_config_961_, 9, v___y_927_);
v___x_962_ = l_Lean_Meta_Context_configKey(v_a_921_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_921_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_977_ = lean_ctor_get(v_a_921_, 6);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_a_921_, 5);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_a_921_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_a_921_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_a_921_, 2);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_a_921_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_a_921_, 0);
lean_dec(v_unused_983_);
v___x_964_ = v_a_921_;
v_isShared_965_ = v_isSharedCheck_976_;
goto v_resetjp_963_;
}
else
{
lean_dec(v_a_921_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_976_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v_key_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_966_ = 2ULL;
v___x_967_ = lean_uint64_shift_right(v___x_962_, v___x_966_);
v___x_968_ = lean_uint64_shift_left(v___x_967_, v___x_966_);
v___x_969_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_927_);
v_key_970_ = lean_uint64_lor(v___x_968_, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_971_, 0, v_config_961_);
lean_ctor_set_uint64(v___x_971_, sizeof(void*)*1, v_key_970_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_971_);
v___x_973_ = v___x_964_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_zetaDeltaSet_951_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_lctx_952_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_localInstances_953_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_defEqCtx_x3f_954_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v_synthPendingDepth_955_);
lean_ctor_set(v_reuseFailAlloc_975_, 6, v_canUnfold_x3f_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*7, v_trackZetaDelta_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*7 + 1, v_univApprox_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*7 + 2, v_inTypeClassResolution_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*7 + 3, v_cacheInferType_959_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v___x_919_, v_e_920_, v___x_973_, v_a_922_, v_a_923_, v_a_924_);
return v___x_974_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalBitVec___private__1_spec__0___boxed(lean_object* v___x_990_, lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalBitVec___private__1_spec__0(v___x_990_, v_e_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v___x_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1(lean_object* v_n_1003_, lean_object* v_e_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; 
lean_inc(v_a_1008_);
lean_inc_ref(v_a_1007_);
lean_inc(v_a_1006_);
lean_inc_ref(v_a_1005_);
v___x_1010_ = lean_whnf(v_e_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2));
v___x_1013_ = lean_unsigned_to_nat(2u);
v___x_1014_ = l_Lean_Expr_isAppOfArity(v_a_1011_, v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1011_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1016_ = lean_nat_pow(v___x_1013_, v_n_1003_);
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_sub(v___x_1016_, v___x_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_nat_add(v___x_1018_, v___x_1017_);
lean_dec(v___x_1018_);
v___x_1020_ = l_Lean_Expr_getAppNumArgs(v_a_1011_);
v___x_1021_ = lean_nat_sub(v___x_1020_, v___x_1017_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_nat_sub(v___x_1021_, v___x_1017_);
lean_dec(v___x_1021_);
v___x_1023_ = l_Lean_Expr_getRevArg_x21(v_a_1011_, v___x_1022_);
lean_dec(v_a_1011_);
v___x_1024_ = l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalBitVec___private__1_spec__0(v___x_1019_, v___x_1023_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v___x_1019_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
v_a_1033_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1024_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1024_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
v_a_1041_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1010_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1010_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(lean_object* v_n_1049_, lean_object* v_e_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_instReduceEvalBitVec___private__1(v_n_1049_, v_e_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_n_1049_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec(lean_object* v_n_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalBitVec___private__1___boxed), 7, 1);
lean_closure_set(v___x_1058_, 0, v_n_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1(lean_object* v_e_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; 
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1074_ = lean_whnf(v_e_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1092_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1092_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1092_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__2));
v___x_1080_ = l_Lean_Expr_isAppOf(v_a_1075_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__4));
v___x_1082_ = l_Lean_Expr_isAppOf(v_a_1075_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_del_object(v___x_1077_);
v___x_1083_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1075_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
v___x_1084_ = lean_box(v___x_1080_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1084_);
v___x_1086_ = v___x_1077_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
v___x_1088_ = lean_box(v___x_1080_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1088_);
v___x_1090_ = v___x_1077_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
v_a_1093_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1074_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1074_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1___boxed(lean_object* v_e_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Meta_instReduceEvalBool___private__1(v_e_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1(lean_object* v_e_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc_ref(v_e_1115_);
v___x_1121_ = lean_whnf(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1174_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1174_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1174_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Expr_constName_x3f(v_a_1122_);
lean_dec(v_a_1122_);
if (lean_obj_tag(v___x_1126_) == 1)
{
lean_object* v_val_1127_; 
v_val_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1127_);
lean_dec_ref(v___x_1126_);
if (lean_obj_tag(v_val_1127_) == 1)
{
lean_object* v_pre_1128_; 
v_pre_1128_ = lean_ctor_get(v_val_1127_, 0);
lean_inc(v_pre_1128_);
if (lean_obj_tag(v_pre_1128_) == 1)
{
lean_object* v_pre_1129_; 
v_pre_1129_ = lean_ctor_get(v_pre_1128_, 0);
lean_inc(v_pre_1129_);
if (lean_obj_tag(v_pre_1129_) == 1)
{
lean_object* v_pre_1130_; 
v_pre_1130_ = lean_ctor_get(v_pre_1129_, 0);
if (lean_obj_tag(v_pre_1130_) == 0)
{
lean_object* v_str_1131_; lean_object* v_str_1132_; lean_object* v_str_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_str_1131_ = lean_ctor_get(v_val_1127_, 1);
lean_inc_ref(v_str_1131_);
lean_dec_ref(v_val_1127_);
v_str_1132_ = lean_ctor_get(v_pre_1128_, 1);
lean_inc_ref(v_str_1132_);
lean_dec_ref(v_pre_1128_);
v_str_1133_ = lean_ctor_get(v_pre_1129_, 1);
lean_inc_ref(v_str_1133_);
lean_dec_ref(v_pre_1129_);
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0));
v___x_1135_ = lean_string_dec_eq(v_str_1133_, v___x_1134_);
lean_dec_ref(v_str_1133_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec_ref(v_str_1132_);
lean_dec_ref(v_str_1131_);
lean_del_object(v___x_1124_);
v___x_1136_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0));
v___x_1138_ = lean_string_dec_eq(v_str_1132_, v___x_1137_);
lean_dec_ref(v_str_1132_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v_str_1131_);
lean_del_object(v___x_1124_);
v___x_1139_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1));
v___x_1141_ = lean_string_dec_eq(v_str_1131_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2));
v___x_1143_ = lean_string_dec_eq(v_str_1131_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3));
v___x_1145_ = lean_string_dec_eq(v_str_1131_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4));
v___x_1147_ = lean_string_dec_eq(v_str_1131_, v___x_1146_);
lean_dec_ref(v_str_1131_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_del_object(v___x_1124_);
v___x_1148_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1148_;
}
else
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_e_1115_);
v___x_1149_ = 3;
v___x_1150_ = lean_box(v___x_1149_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1150_);
v___x_1152_ = v___x_1124_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec_ref(v_str_1131_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_e_1115_);
v___x_1154_ = 2;
v___x_1155_ = lean_box(v___x_1154_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1155_);
v___x_1157_ = v___x_1124_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec_ref(v_str_1131_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_e_1115_);
v___x_1159_ = 1;
v___x_1160_ = lean_box(v___x_1159_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1160_);
v___x_1162_ = v___x_1124_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_dec_ref(v_str_1131_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_e_1115_);
v___x_1164_ = 0;
v___x_1165_ = lean_box(v___x_1164_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1165_);
v___x_1167_ = v___x_1124_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
else
{
lean_object* v___x_1169_; 
lean_dec_ref(v_pre_1129_);
lean_dec_ref(v_pre_1128_);
lean_dec_ref(v_val_1127_);
lean_del_object(v___x_1124_);
v___x_1169_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1170_; 
lean_dec_ref(v_pre_1128_);
lean_dec(v_pre_1129_);
lean_dec_ref(v_val_1127_);
lean_del_object(v___x_1124_);
v___x_1170_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1170_;
}
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_pre_1128_);
lean_dec_ref(v_val_1127_);
lean_del_object(v___x_1124_);
v___x_1171_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; 
lean_dec(v_val_1127_);
lean_del_object(v___x_1124_);
v___x_1172_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1172_;
}
}
else
{
lean_object* v___x_1173_; 
lean_dec(v___x_1126_);
lean_del_object(v___x_1124_);
v___x_1173_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_e_1115_);
v_a_1175_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1121_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1121_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(lean_object* v_e_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(v_e_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1(lean_object* v_e_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1209_; 
lean_inc(v_a_1207_);
lean_inc_ref(v_a_1206_);
lean_inc(v_a_1205_);
lean_inc_ref(v_a_1204_);
v___x_1209_ = lean_whnf(v_e_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2));
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = l_Lean_Expr_isAppOfArity(v_a_1210_, v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4));
v___x_1215_ = l_Lean_Expr_isAppOfArity(v_a_1210_, v___x_1214_, v___x_1212_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1210_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = l_Lean_Expr_getAppNumArgs(v_a_1210_);
v___x_1218_ = lean_nat_sub(v___x_1217_, v___x_1212_);
lean_dec(v___x_1217_);
v___x_1219_ = l_Lean_Expr_getRevArg_x21(v_a_1210_, v___x_1218_);
lean_dec(v_a_1210_);
v___x_1220_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_1219_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_a_1230_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1220_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1220_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = l_Lean_Expr_getAppNumArgs(v_a_1210_);
v___x_1239_ = lean_nat_sub(v___x_1238_, v___x_1212_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Lean_Expr_getRevArg_x21(v_a_1210_, v___x_1239_);
lean_dec(v_a_1210_);
v___x_1241_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_1240_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_a_1251_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1241_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1241_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
v_a_1259_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1209_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1209_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(lean_object* v_e_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_instReduceEvalLiteral___private__1(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0(lean_object* v_e_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v___y_1283_; lean_object* v___x_1342_; uint8_t v_transparency_1343_; uint8_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = l_Lean_Meta_Context_config(v_a_1277_);
v_transparency_1343_ = lean_ctor_get_uint8(v___x_1342_, 9);
lean_dec_ref(v___x_1342_);
v___x_1344_ = 1;
v___x_1345_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
v___y_1283_ = v_transparency_1343_;
goto v___jp_1282_;
}
else
{
v___y_1283_ = v___x_1344_;
goto v___jp_1282_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; uint8_t v_foApprox_1285_; uint8_t v_ctxApprox_1286_; uint8_t v_quasiPatternApprox_1287_; uint8_t v_constApprox_1288_; uint8_t v_isDefEqStuckEx_1289_; uint8_t v_unificationHints_1290_; uint8_t v_proofIrrelevance_1291_; uint8_t v_assignSyntheticOpaque_1292_; uint8_t v_offsetCnstrs_1293_; uint8_t v_etaStruct_1294_; uint8_t v_univApprox_1295_; uint8_t v_iota_1296_; uint8_t v_beta_1297_; uint8_t v_proj_1298_; uint8_t v_zeta_1299_; uint8_t v_zetaDelta_1300_; uint8_t v_zetaUnused_1301_; uint8_t v_zetaHave_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1341_; 
v___x_1284_ = l_Lean_Meta_Context_config(v_a_1277_);
v_foApprox_1285_ = lean_ctor_get_uint8(v___x_1284_, 0);
v_ctxApprox_1286_ = lean_ctor_get_uint8(v___x_1284_, 1);
v_quasiPatternApprox_1287_ = lean_ctor_get_uint8(v___x_1284_, 2);
v_constApprox_1288_ = lean_ctor_get_uint8(v___x_1284_, 3);
v_isDefEqStuckEx_1289_ = lean_ctor_get_uint8(v___x_1284_, 4);
v_unificationHints_1290_ = lean_ctor_get_uint8(v___x_1284_, 5);
v_proofIrrelevance_1291_ = lean_ctor_get_uint8(v___x_1284_, 6);
v_assignSyntheticOpaque_1292_ = lean_ctor_get_uint8(v___x_1284_, 7);
v_offsetCnstrs_1293_ = lean_ctor_get_uint8(v___x_1284_, 8);
v_etaStruct_1294_ = lean_ctor_get_uint8(v___x_1284_, 10);
v_univApprox_1295_ = lean_ctor_get_uint8(v___x_1284_, 11);
v_iota_1296_ = lean_ctor_get_uint8(v___x_1284_, 12);
v_beta_1297_ = lean_ctor_get_uint8(v___x_1284_, 13);
v_proj_1298_ = lean_ctor_get_uint8(v___x_1284_, 14);
v_zeta_1299_ = lean_ctor_get_uint8(v___x_1284_, 15);
v_zetaDelta_1300_ = lean_ctor_get_uint8(v___x_1284_, 16);
v_zetaUnused_1301_ = lean_ctor_get_uint8(v___x_1284_, 17);
v_zetaHave_1302_ = lean_ctor_get_uint8(v___x_1284_, 18);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1304_ = v___x_1284_;
v_isShared_1305_ = v_isSharedCheck_1341_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v___x_1284_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1341_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint8_t v_trackZetaDelta_1306_; lean_object* v_zetaDeltaSet_1307_; lean_object* v_lctx_1308_; lean_object* v_localInstances_1309_; lean_object* v_defEqCtx_x3f_1310_; lean_object* v_synthPendingDepth_1311_; lean_object* v_canUnfold_x3f_1312_; uint8_t v_univApprox_1313_; uint8_t v_inTypeClassResolution_1314_; uint8_t v_cacheInferType_1315_; lean_object* v_config_1317_; 
v_trackZetaDelta_1306_ = lean_ctor_get_uint8(v_a_1277_, sizeof(void*)*7);
v_zetaDeltaSet_1307_ = lean_ctor_get(v_a_1277_, 1);
lean_inc(v_zetaDeltaSet_1307_);
v_lctx_1308_ = lean_ctor_get(v_a_1277_, 2);
lean_inc_ref(v_lctx_1308_);
v_localInstances_1309_ = lean_ctor_get(v_a_1277_, 3);
lean_inc_ref(v_localInstances_1309_);
v_defEqCtx_x3f_1310_ = lean_ctor_get(v_a_1277_, 4);
lean_inc(v_defEqCtx_x3f_1310_);
v_synthPendingDepth_1311_ = lean_ctor_get(v_a_1277_, 5);
lean_inc(v_synthPendingDepth_1311_);
v_canUnfold_x3f_1312_ = lean_ctor_get(v_a_1277_, 6);
lean_inc(v_canUnfold_x3f_1312_);
v_univApprox_1313_ = lean_ctor_get_uint8(v_a_1277_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1314_ = lean_ctor_get_uint8(v_a_1277_, sizeof(void*)*7 + 2);
v_cacheInferType_1315_ = lean_ctor_get_uint8(v_a_1277_, sizeof(void*)*7 + 3);
if (v_isShared_1305_ == 0)
{
v_config_1317_ = v___x_1304_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 0, v_foApprox_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 1, v_ctxApprox_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 2, v_quasiPatternApprox_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 3, v_constApprox_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 4, v_isDefEqStuckEx_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 5, v_unificationHints_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 6, v_proofIrrelevance_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 7, v_assignSyntheticOpaque_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 8, v_offsetCnstrs_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 10, v_etaStruct_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 11, v_univApprox_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 12, v_iota_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 13, v_beta_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 14, v_proj_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 15, v_zeta_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 16, v_zetaDelta_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 17, v_zetaUnused_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, 18, v_zetaHave_1302_);
v_config_1317_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
uint64_t v___x_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1332_; 
lean_ctor_set_uint8(v_config_1317_, 9, v___y_1283_);
v___x_1318_ = l_Lean_Meta_Context_configKey(v_a_1277_);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1277_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1333_ = lean_ctor_get(v_a_1277_, 6);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v_a_1277_, 5);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_a_1277_, 4);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_a_1277_, 3);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_a_1277_, 2);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_a_1277_, 1);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_a_1277_, 0);
lean_dec(v_unused_1339_);
v___x_1320_ = v_a_1277_;
v_isShared_1321_ = v_isSharedCheck_1332_;
goto v_resetjp_1319_;
}
else
{
lean_dec(v_a_1277_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1332_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint64_t v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; uint64_t v_key_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1322_ = 2ULL;
v___x_1323_ = lean_uint64_shift_right(v___x_1318_, v___x_1322_);
v___x_1324_ = lean_uint64_shift_left(v___x_1323_, v___x_1322_);
v___x_1325_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1283_);
v_key_1326_ = lean_uint64_lor(v___x_1324_, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1327_, 0, v_config_1317_);
lean_ctor_set_uint64(v___x_1327_, sizeof(void*)*1, v_key_1326_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1327_);
v___x_1329_ = v___x_1320_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_zetaDeltaSet_1307_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_lctx_1308_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_localInstances_1309_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_defEqCtx_x3f_1310_);
lean_ctor_set(v_reuseFailAlloc_1331_, 5, v_synthPendingDepth_1311_);
lean_ctor_set(v_reuseFailAlloc_1331_, 6, v_canUnfold_x3f_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*7, v_trackZetaDelta_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*7 + 1, v_univApprox_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*7 + 3, v_cacheInferType_1315_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_1276_, v___x_1329_, v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0___boxed(lean_object* v_e_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0(v_e_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; 
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
v___x_1364_ = lean_whnf(v_e_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
v___x_1366_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = l_Lean_Expr_isAppOfArity(v_a_1365_, v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1365_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = l_Lean_Expr_getAppNumArgs(v_a_1365_);
v___x_1371_ = lean_nat_sub(v___x_1370_, v___x_1367_);
lean_dec(v___x_1370_);
v___x_1372_ = l_Lean_Expr_getRevArg_x21(v_a_1365_, v___x_1371_);
lean_dec(v_a_1365_);
v___x_1373_ = l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0(v___x_1372_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1373_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1373_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
v_a_1390_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1364_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1364_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object* v_e_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_instReduceEvalMVarId___private__1(v_e_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1(lean_object* v_e_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1418_; 
lean_inc(v_a_1416_);
lean_inc_ref(v_a_1415_);
lean_inc(v_a_1414_);
lean_inc_ref(v_a_1413_);
v___x_1418_ = lean_whnf(v_e_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = l_Lean_Expr_isAppOfArity(v_a_1419_, v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1419_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
return v___x_1423_;
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = l_Lean_Expr_getAppNumArgs(v_a_1419_);
v___x_1425_ = lean_nat_sub(v___x_1424_, v___x_1421_);
lean_dec(v___x_1424_);
v___x_1426_ = l_Lean_Expr_getRevArg_x21(v_a_1419_, v___x_1425_);
lean_dec(v_a_1419_);
v___x_1427_ = l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0(v___x_1426_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1427_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1427_);
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
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
v_a_1444_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1418_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1418_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(lean_object* v_e_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(v_e_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1(lean_object* v_e_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; 
lean_inc(v_a_1470_);
lean_inc_ref(v_a_1469_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1472_ = lean_whnf(v_e_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1475_ = lean_unsigned_to_nat(1u);
v___x_1476_ = l_Lean_Expr_isAppOfArity(v_a_1473_, v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1473_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = l_Lean_Expr_getAppNumArgs(v_a_1473_);
v___x_1479_ = lean_nat_sub(v___x_1478_, v___x_1475_);
lean_dec(v___x_1478_);
v___x_1480_ = l_Lean_Expr_getRevArg_x21(v_a_1473_, v___x_1479_);
lean_dec(v_a_1473_);
v___x_1481_ = l_Lean_Meta_reduceEval___at___00Lean_Meta_instReduceEvalMVarId___private__1_spec__0(v___x_1480_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_a_1490_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1481_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1481_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
v_a_1498_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1472_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1472_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(lean_object* v_e_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Meta_instReduceEvalFVarId___private__1(v_e_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v_res_1512_;
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
