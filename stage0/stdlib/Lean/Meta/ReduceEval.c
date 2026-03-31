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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
uint8_t v___y_9_; lean_object* v___x_55_; uint8_t v_transparency_56_; uint8_t v___x_57_; uint8_t v___x_58_; 
v___x_55_ = l_Lean_Meta_Context_config(v_a_3_);
v_transparency_56_ = lean_ctor_get_uint8(v___x_55_, 9);
lean_dec_ref(v___x_55_);
v___x_57_ = 1;
v___x_58_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_56_, v___x_57_);
if (v___x_58_ == 0)
{
v___y_9_ = v_transparency_56_;
goto v___jp_8_;
}
else
{
v___y_9_ = v___x_57_;
goto v___jp_8_;
}
v___jp_8_:
{
lean_object* v___x_10_; uint8_t v_foApprox_11_; uint8_t v_ctxApprox_12_; uint8_t v_quasiPatternApprox_13_; uint8_t v_constApprox_14_; uint8_t v_isDefEqStuckEx_15_; uint8_t v_unificationHints_16_; uint8_t v_proofIrrelevance_17_; uint8_t v_assignSyntheticOpaque_18_; uint8_t v_offsetCnstrs_19_; uint8_t v_etaStruct_20_; uint8_t v_univApprox_21_; uint8_t v_iota_22_; uint8_t v_beta_23_; uint8_t v_proj_24_; uint8_t v_zeta_25_; uint8_t v_zetaDelta_26_; uint8_t v_zetaUnused_27_; uint8_t v_zetaHave_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_54_; 
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
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_54_ == 0)
{
v___x_30_ = v___x_10_;
v_isShared_31_ = v_isSharedCheck_54_;
goto v_resetjp_29_;
}
else
{
lean_dec(v___x_10_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_54_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v_trackZetaDelta_32_; lean_object* v_zetaDeltaSet_33_; lean_object* v_lctx_34_; lean_object* v_localInstances_35_; lean_object* v_defEqCtx_x3f_36_; lean_object* v_synthPendingDepth_37_; lean_object* v_canUnfold_x3f_38_; uint8_t v_univApprox_39_; uint8_t v_inTypeClassResolution_40_; uint8_t v_cacheInferType_41_; lean_object* v_config_43_; 
v_trackZetaDelta_32_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*7);
v_zetaDeltaSet_33_ = lean_ctor_get(v_a_3_, 1);
v_lctx_34_ = lean_ctor_get(v_a_3_, 2);
v_localInstances_35_ = lean_ctor_get(v_a_3_, 3);
v_defEqCtx_x3f_36_ = lean_ctor_get(v_a_3_, 4);
v_synthPendingDepth_37_ = lean_ctor_get(v_a_3_, 5);
v_canUnfold_x3f_38_ = lean_ctor_get(v_a_3_, 6);
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
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 0, v_foApprox_11_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 1, v_ctxApprox_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 2, v_quasiPatternApprox_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 3, v_constApprox_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 4, v_isDefEqStuckEx_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 5, v_unificationHints_16_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 6, v_proofIrrelevance_17_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 7, v_assignSyntheticOpaque_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 8, v_offsetCnstrs_19_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 10, v_etaStruct_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 11, v_univApprox_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 12, v_iota_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 13, v_beta_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 14, v_proj_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 15, v_zeta_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 16, v_zetaDelta_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 17, v_zetaUnused_27_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, 18, v_zetaHave_28_);
v_config_43_ = v_reuseFailAlloc_53_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v_key_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
lean_ctor_set_uint8(v_config_43_, 9, v___y_9_);
v___x_44_ = l_Lean_Meta_Context_configKey(v_a_3_);
v___x_45_ = 2ULL;
v___x_46_ = lean_uint64_shift_right(v___x_44_, v___x_45_);
v___x_47_ = lean_uint64_shift_left(v___x_46_, v___x_45_);
v___x_48_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_9_);
v_key_49_ = lean_uint64_lor(v___x_47_, v___x_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_50_, 0, v_config_43_);
lean_ctor_set_uint64(v___x_50_, sizeof(void*)*1, v_key_49_);
lean_inc(v_canUnfold_x3f_38_);
lean_inc(v_synthPendingDepth_37_);
lean_inc(v_defEqCtx_x3f_36_);
lean_inc_ref(v_localInstances_35_);
lean_inc_ref(v_lctx_34_);
lean_inc(v_zetaDeltaSet_33_);
v___x_51_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_zetaDeltaSet_33_);
lean_ctor_set(v___x_51_, 2, v_lctx_34_);
lean_ctor_set(v___x_51_, 3, v_localInstances_35_);
lean_ctor_set(v___x_51_, 4, v_defEqCtx_x3f_36_);
lean_ctor_set(v___x_51_, 5, v_synthPendingDepth_37_);
lean_ctor_set(v___x_51_, 6, v_canUnfold_x3f_38_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*7, v_trackZetaDelta_32_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*7 + 1, v_univApprox_39_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*7 + 2, v_inTypeClassResolution_40_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*7 + 3, v_cacheInferType_41_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
v___x_52_ = lean_apply_6(v_inst_1_, v_e_2_, v___x_51_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object* v_inst_59_, lean_object* v_e_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_reduceEval___redArg(v_inst_59_, v_e_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_e_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Meta_reduceEval___redArg(v_inst_68_, v_e_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_e_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_reduceEval(v_00_u03b1_76_, v_inst_77_, v_e_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_mctx_94_; lean_object* v_lctx_95_; lean_object* v_options_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_87_);
v_mctx_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_94_);
lean_dec(v___x_93_);
v_lctx_95_ = lean_ctor_get(v___y_86_, 2);
v_options_96_ = lean_ctor_get(v___y_88_, 2);
lean_inc_ref(v_options_96_);
lean_inc_ref(v_lctx_95_);
v___x_97_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_97_, 0, v_env_92_);
lean_ctor_set(v___x_97_, 1, v_mctx_94_);
lean_ctor_set(v___x_97_, 2, v_lctx_95_);
lean_ctor_set(v___x_97_, 3, v_options_96_);
v___x_98_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_msgData_85_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(lean_object* v_msgData_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_ref_113_; lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_ref_113_ = lean_ctor_get(v___y_110_, 5);
v___x_114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_inc(v_ref_113_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_ref_113_);
lean_ctor_set(v___x_119_, 1, v_a_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 1);
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0));
v___x_133_ = l_Lean_stringToMessageData(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object* v_e_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1, &l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once, _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
v___x_141_ = l_Lean_indentExpr(v_e_134_);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_142_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object* v_e_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* v_00_u03b1_151_, lean_object* v_e_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* v_00_u03b1_159_, lean_object* v_e_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(v_00_u03b1_159_, v_e_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(lean_object* v_00_u03b1_167_, lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(lean_object* v_00_u03b1_175_, lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_175_, v_msg_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1(lean_object* v_e_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
lean_inc(v_a_187_);
lean_inc_ref(v_a_186_);
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
v___x_189_ = lean_whnf(v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc_n(v_a_190_, 2);
lean_dec_ref(v___x_189_);
v___x_191_ = l_Lean_Meta_evalNat(v_a_190_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_201_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
if (lean_obj_tag(v_a_192_) == 1)
{
lean_object* v_val_196_; lean_object* v___x_198_; 
lean_dec(v_a_190_);
v_val_196_ = lean_ctor_get(v_a_192_, 0);
lean_inc(v_val_196_);
lean_dec_ref(v_a_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v_val_196_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_val_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
else
{
lean_object* v___x_200_; 
lean_del_object(v___x_194_);
lean_dec(v_a_192_);
v___x_200_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_190_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_200_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_190_);
v_a_202_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_191_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_191_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_189_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_189_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___private__1___boxed(lean_object* v_e_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Meta_instReduceEvalNat___private__1(v_e_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object* v_e_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; 
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc(v___y_227_);
lean_inc_ref(v___y_226_);
v___x_231_ = lean_whnf(v_e_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_n(v_a_232_, 2);
lean_dec_ref(v___x_231_);
v___x_233_ = l_Lean_Meta_evalNat(v_a_232_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_243_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_243_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
if (lean_obj_tag(v_a_234_) == 1)
{
lean_object* v_val_238_; lean_object* v___x_240_; 
lean_dec(v_a_232_);
v_val_238_ = lean_ctor_get(v_a_234_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v_a_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_val_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_val_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_242_; 
lean_del_object(v___x_236_);
lean_dec(v_a_234_);
v___x_242_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_232_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_242_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_a_232_);
v_a_244_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_233_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_231_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_231_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0___boxed(lean_object* v_e_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_instReduceEvalNat___lam__0(v_e_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg(lean_object* v_inst_278_, lean_object* v_e_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; 
lean_inc(v_a_283_);
lean_inc_ref(v_a_282_);
lean_inc(v_a_281_);
lean_inc_ref(v_a_280_);
v___x_285_ = lean_whnf(v_e_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_330_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_330_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_330_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_330_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___y_291_; lean_object* v___x_312_; 
v___x_312_ = l_Lean_Expr_getAppFn(v_a_286_);
if (lean_obj_tag(v___x_312_) == 4)
{
lean_object* v_declName_313_; lean_object* v___x_314_; uint8_t v___y_316_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_declName_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_declName_313_);
lean_dec_ref(v___x_312_);
v___x_314_ = l_Lean_Expr_getAppNumArgs(v_a_286_);
v___x_325_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_326_ = lean_name_eq(v_declName_313_, v___x_325_);
if (v___x_326_ == 0)
{
v___y_316_ = v___x_326_;
goto v___jp_315_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_nat_dec_eq(v___x_314_, v___x_327_);
v___y_316_ = v___x_328_;
goto v___jp_315_;
}
v___jp_315_:
{
if (v___y_316_ == 0)
{
lean_object* v___x_317_; uint8_t v___x_318_; 
lean_del_object(v___x_288_);
v___x_317_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_318_ = lean_name_eq(v_declName_313_, v___x_317_);
lean_dec(v_declName_313_);
if (v___x_318_ == 0)
{
lean_dec(v___x_314_);
v___y_291_ = v___x_318_;
goto v___jp_290_;
}
else
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_dec_eq(v___x_314_, v___x_319_);
lean_dec(v___x_314_);
v___y_291_ = v___x_320_;
goto v___jp_290_;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_323_; 
lean_dec(v___x_314_);
lean_dec(v_declName_313_);
lean_dec(v_a_286_);
lean_dec_ref(v_inst_278_);
v___x_321_ = lean_box(0);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_321_);
v___x_323_ = v___x_288_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v___x_329_; 
lean_dec_ref(v___x_312_);
lean_del_object(v___x_288_);
lean_dec_ref(v_inst_278_);
v___x_329_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_286_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
return v___x_329_;
}
v___jp_290_:
{
if (v___y_291_ == 0)
{
lean_object* v___x_292_; 
lean_dec_ref(v_inst_278_);
v___x_292_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_286_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = l_Lean_Expr_appArg_x21(v_a_286_);
lean_dec(v_a_286_);
v___x_294_ = l_Lean_Meta_reduceEval___redArg(v_inst_278_, v___x_293_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_a_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_a_304_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_294_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_294_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
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
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_inst_278_);
v_a_331_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_285_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_285_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(lean_object* v_inst_339_, lean_object* v_e_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(v_inst_339_, v_e_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___private__1(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; 
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
v___x_355_ = lean_whnf(v_e_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_400_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_400_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_400_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_400_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___y_361_; lean_object* v___x_382_; 
v___x_382_ = l_Lean_Expr_getAppFn(v_a_356_);
if (lean_obj_tag(v___x_382_) == 4)
{
lean_object* v_declName_383_; lean_object* v___x_384_; uint8_t v___y_386_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_declName_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_declName_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = l_Lean_Expr_getAppNumArgs(v_a_356_);
v___x_395_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4));
v___x_396_ = lean_name_eq(v_declName_383_, v___x_395_);
if (v___x_396_ == 0)
{
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
else
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_nat_dec_eq(v___x_384_, v___x_397_);
v___y_386_ = v___x_398_;
goto v___jp_385_;
}
v___jp_385_:
{
if (v___y_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
lean_del_object(v___x_358_);
v___x_387_ = ((lean_object*)(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2));
v___x_388_ = lean_name_eq(v_declName_383_, v___x_387_);
lean_dec(v_declName_383_);
if (v___x_388_ == 0)
{
lean_dec(v___x_384_);
v___y_361_ = v___x_388_;
goto v___jp_360_;
}
else
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_dec_eq(v___x_384_, v___x_389_);
lean_dec(v___x_384_);
v___y_361_ = v___x_390_;
goto v___jp_360_;
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_393_; 
lean_dec(v___x_384_);
lean_dec(v_declName_383_);
lean_dec(v_a_356_);
lean_dec_ref(v_inst_348_);
v___x_391_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_391_);
v___x_393_ = v___x_358_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v___x_399_; 
lean_dec_ref(v___x_382_);
lean_del_object(v___x_358_);
lean_dec_ref(v_inst_348_);
v___x_399_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_356_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_399_;
}
v___jp_360_:
{
if (v___y_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v_inst_348_);
v___x_362_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_356_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = l_Lean_Expr_appArg_x21(v_a_356_);
lean_dec(v_a_356_);
v___x_364_ = l_Lean_Meta_reduceEval___redArg(v_inst_348_, v___x_363_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
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
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_inst_348_);
v_a_401_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_355_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_355_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object* v_inst_418_, lean_object* v_e_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
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
lean_dec_ref(v___x_452_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(lean_object* v_inst_479_, lean_object* v_e_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(v_inst_479_, v_e_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object* v_inst_487_){
_start:
{
lean_object* v___f_488_; 
v___f_488_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_488_, 0, v_inst_487_);
return v___f_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* v_00_u03b1_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v___f_491_; 
v___f_491_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_491_, 0, v_inst_490_);
return v___f_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1(lean_object* v_e_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc_ref(v_e_492_);
v___x_498_ = lean_whnf(v_e_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_510_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_510_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 9)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v_a_499_, 0);
lean_inc_ref(v_a_503_);
lean_dec_ref(v_a_499_);
if (lean_obj_tag(v_a_503_) == 1)
{
lean_object* v_val_504_; lean_object* v___x_506_; 
lean_dec_ref(v_e_492_);
v_val_504_ = lean_ctor_get(v_a_503_, 0);
lean_inc_ref(v_val_504_);
lean_dec_ref(v_a_503_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_val_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_val_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v___x_508_; 
lean_dec_ref(v_a_503_);
lean_del_object(v___x_501_);
v___x_508_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v___x_508_;
}
}
else
{
lean_object* v___x_509_; 
lean_del_object(v___x_501_);
lean_dec(v_a_499_);
v___x_509_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v___x_509_;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_e_492_);
v_a_511_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_498_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_498_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___private__1___boxed(lean_object* v_e_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Meta_instReduceEvalString___private__1(v_e_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object* v_e_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; 
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
lean_inc_ref(v_e_526_);
v___x_532_ = lean_whnf(v_e_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
if (lean_obj_tag(v_a_533_) == 9)
{
lean_object* v_a_537_; 
v_a_537_ = lean_ctor_get(v_a_533_, 0);
lean_inc_ref(v_a_537_);
lean_dec_ref(v_a_533_);
if (lean_obj_tag(v_a_537_) == 1)
{
lean_object* v_val_538_; lean_object* v___x_540_; 
lean_dec_ref(v_e_526_);
v_val_538_ = lean_ctor_get(v_a_537_, 0);
lean_inc_ref(v_val_538_);
lean_dec_ref(v_a_537_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_val_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_val_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
else
{
lean_object* v___x_542_; 
lean_dec_ref(v_a_537_);
lean_del_object(v___x_535_);
v___x_542_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_542_;
}
}
else
{
lean_object* v___x_543_; 
lean_del_object(v___x_535_);
lean_dec(v_a_533_);
v___x_543_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_543_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_e_526_);
v_a_545_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_532_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_532_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0___boxed(lean_object* v_e_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_instReduceEvalString___lam__0(v_e_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object* v_e_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
uint8_t v___y_569_; lean_object* v___x_643_; uint8_t v_transparency_644_; uint8_t v___x_645_; uint8_t v___x_646_; 
v___x_643_ = l_Lean_Meta_Context_config(v_a_563_);
v_transparency_644_ = lean_ctor_get_uint8(v___x_643_, 9);
lean_dec_ref(v___x_643_);
v___x_645_ = 1;
v___x_646_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_644_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_569_ = v_transparency_644_;
goto v___jp_568_;
}
else
{
v___y_569_ = v___x_645_;
goto v___jp_568_;
}
v___jp_568_:
{
lean_object* v___x_570_; uint8_t v_foApprox_571_; uint8_t v_ctxApprox_572_; uint8_t v_quasiPatternApprox_573_; uint8_t v_constApprox_574_; uint8_t v_isDefEqStuckEx_575_; uint8_t v_unificationHints_576_; uint8_t v_proofIrrelevance_577_; uint8_t v_assignSyntheticOpaque_578_; uint8_t v_offsetCnstrs_579_; uint8_t v_etaStruct_580_; uint8_t v_univApprox_581_; uint8_t v_iota_582_; uint8_t v_beta_583_; uint8_t v_proj_584_; uint8_t v_zeta_585_; uint8_t v_zetaDelta_586_; uint8_t v_zetaUnused_587_; uint8_t v_zetaHave_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_642_; 
v___x_570_ = l_Lean_Meta_Context_config(v_a_563_);
v_foApprox_571_ = lean_ctor_get_uint8(v___x_570_, 0);
v_ctxApprox_572_ = lean_ctor_get_uint8(v___x_570_, 1);
v_quasiPatternApprox_573_ = lean_ctor_get_uint8(v___x_570_, 2);
v_constApprox_574_ = lean_ctor_get_uint8(v___x_570_, 3);
v_isDefEqStuckEx_575_ = lean_ctor_get_uint8(v___x_570_, 4);
v_unificationHints_576_ = lean_ctor_get_uint8(v___x_570_, 5);
v_proofIrrelevance_577_ = lean_ctor_get_uint8(v___x_570_, 6);
v_assignSyntheticOpaque_578_ = lean_ctor_get_uint8(v___x_570_, 7);
v_offsetCnstrs_579_ = lean_ctor_get_uint8(v___x_570_, 8);
v_etaStruct_580_ = lean_ctor_get_uint8(v___x_570_, 10);
v_univApprox_581_ = lean_ctor_get_uint8(v___x_570_, 11);
v_iota_582_ = lean_ctor_get_uint8(v___x_570_, 12);
v_beta_583_ = lean_ctor_get_uint8(v___x_570_, 13);
v_proj_584_ = lean_ctor_get_uint8(v___x_570_, 14);
v_zeta_585_ = lean_ctor_get_uint8(v___x_570_, 15);
v_zetaDelta_586_ = lean_ctor_get_uint8(v___x_570_, 16);
v_zetaUnused_587_ = lean_ctor_get_uint8(v___x_570_, 17);
v_zetaHave_588_ = lean_ctor_get_uint8(v___x_570_, 18);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_642_ == 0)
{
v___x_590_ = v___x_570_;
v_isShared_591_ = v_isSharedCheck_642_;
goto v_resetjp_589_;
}
else
{
lean_dec(v___x_570_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_642_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v_trackZetaDelta_592_; lean_object* v_zetaDeltaSet_593_; lean_object* v_lctx_594_; lean_object* v_localInstances_595_; lean_object* v_defEqCtx_x3f_596_; lean_object* v_synthPendingDepth_597_; lean_object* v_canUnfold_x3f_598_; uint8_t v_univApprox_599_; uint8_t v_inTypeClassResolution_600_; uint8_t v_cacheInferType_601_; lean_object* v_config_603_; 
v_trackZetaDelta_592_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*7);
v_zetaDeltaSet_593_ = lean_ctor_get(v_a_563_, 1);
v_lctx_594_ = lean_ctor_get(v_a_563_, 2);
v_localInstances_595_ = lean_ctor_get(v_a_563_, 3);
v_defEqCtx_x3f_596_ = lean_ctor_get(v_a_563_, 4);
v_synthPendingDepth_597_ = lean_ctor_get(v_a_563_, 5);
v_canUnfold_x3f_598_ = lean_ctor_get(v_a_563_, 6);
v_univApprox_599_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_600_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*7 + 2);
v_cacheInferType_601_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*7 + 3);
if (v_isShared_591_ == 0)
{
v_config_603_ = v___x_590_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 0, v_foApprox_571_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 1, v_ctxApprox_572_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 2, v_quasiPatternApprox_573_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 3, v_constApprox_574_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 4, v_isDefEqStuckEx_575_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 5, v_unificationHints_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 6, v_proofIrrelevance_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 7, v_assignSyntheticOpaque_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 8, v_offsetCnstrs_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 10, v_etaStruct_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 11, v_univApprox_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 12, v_iota_582_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 13, v_beta_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 14, v_proj_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 15, v_zeta_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 16, v_zetaDelta_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 17, v_zetaUnused_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, 18, v_zetaHave_588_);
v_config_603_ = v_reuseFailAlloc_641_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v_key_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_ctor_set_uint8(v_config_603_, 9, v___y_569_);
v___x_604_ = l_Lean_Meta_Context_configKey(v_a_563_);
v___x_605_ = 2ULL;
v___x_606_ = lean_uint64_shift_right(v___x_604_, v___x_605_);
v___x_607_ = lean_uint64_shift_left(v___x_606_, v___x_605_);
v___x_608_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_569_);
v_key_609_ = lean_uint64_lor(v___x_607_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_610_, 0, v_config_603_);
lean_ctor_set_uint64(v___x_610_, sizeof(void*)*1, v_key_609_);
lean_inc(v_canUnfold_x3f_598_);
lean_inc(v_synthPendingDepth_597_);
lean_inc(v_defEqCtx_x3f_596_);
lean_inc_ref(v_localInstances_595_);
lean_inc_ref(v_lctx_594_);
lean_inc(v_zetaDeltaSet_593_);
v___x_611_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_zetaDeltaSet_593_);
lean_ctor_set(v___x_611_, 2, v_lctx_594_);
lean_ctor_set(v___x_611_, 3, v_localInstances_595_);
lean_ctor_set(v___x_611_, 4, v_defEqCtx_x3f_596_);
lean_ctor_set(v___x_611_, 5, v_synthPendingDepth_597_);
lean_ctor_set(v___x_611_, 6, v_canUnfold_x3f_598_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*7, v_trackZetaDelta_592_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*7 + 1, v_univApprox_599_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*7 + 2, v_inTypeClassResolution_600_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*7 + 3, v_cacheInferType_601_);
lean_inc(v_a_566_);
lean_inc_ref(v_a_565_);
lean_inc(v_a_564_);
lean_inc_ref(v___x_611_);
v___x_612_ = lean_whnf(v_e_562_, v___x_611_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_n(v_a_613_, 2);
lean_dec_ref(v___x_612_);
v___x_614_ = l_Lean_Meta_evalNat(v_a_613_, v___x_611_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_624_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_624_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
if (lean_obj_tag(v_a_615_) == 1)
{
lean_object* v_val_619_; lean_object* v___x_621_; 
lean_dec(v_a_613_);
lean_dec_ref(v___x_611_);
v_val_619_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_val_619_);
lean_dec_ref(v_a_615_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_val_619_);
v___x_621_ = v___x_617_;
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
lean_del_object(v___x_617_);
lean_dec(v_a_615_);
v___x_623_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_613_, v___x_611_, v_a_564_, v_a_565_, v_a_566_);
lean_dec_ref(v___x_611_);
return v___x_623_;
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_613_);
lean_dec_ref(v___x_611_);
v_a_625_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_614_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_614_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___x_611_);
v_a_633_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_612_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_612_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object* v_e_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object* v_e_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
uint8_t v___y_661_; lean_object* v___x_727_; uint8_t v_transparency_728_; uint8_t v___x_729_; uint8_t v___x_730_; 
v___x_727_ = l_Lean_Meta_Context_config(v_a_655_);
v_transparency_728_ = lean_ctor_get_uint8(v___x_727_, 9);
lean_dec_ref(v___x_727_);
v___x_729_ = 1;
v___x_730_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_728_, v___x_729_);
if (v___x_730_ == 0)
{
v___y_661_ = v_transparency_728_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___x_729_;
goto v___jp_660_;
}
v___jp_660_:
{
lean_object* v___x_662_; uint8_t v_foApprox_663_; uint8_t v_ctxApprox_664_; uint8_t v_quasiPatternApprox_665_; uint8_t v_constApprox_666_; uint8_t v_isDefEqStuckEx_667_; uint8_t v_unificationHints_668_; uint8_t v_proofIrrelevance_669_; uint8_t v_assignSyntheticOpaque_670_; uint8_t v_offsetCnstrs_671_; uint8_t v_etaStruct_672_; uint8_t v_univApprox_673_; uint8_t v_iota_674_; uint8_t v_beta_675_; uint8_t v_proj_676_; uint8_t v_zeta_677_; uint8_t v_zetaDelta_678_; uint8_t v_zetaUnused_679_; uint8_t v_zetaHave_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_726_; 
v___x_662_ = l_Lean_Meta_Context_config(v_a_655_);
v_foApprox_663_ = lean_ctor_get_uint8(v___x_662_, 0);
v_ctxApprox_664_ = lean_ctor_get_uint8(v___x_662_, 1);
v_quasiPatternApprox_665_ = lean_ctor_get_uint8(v___x_662_, 2);
v_constApprox_666_ = lean_ctor_get_uint8(v___x_662_, 3);
v_isDefEqStuckEx_667_ = lean_ctor_get_uint8(v___x_662_, 4);
v_unificationHints_668_ = lean_ctor_get_uint8(v___x_662_, 5);
v_proofIrrelevance_669_ = lean_ctor_get_uint8(v___x_662_, 6);
v_assignSyntheticOpaque_670_ = lean_ctor_get_uint8(v___x_662_, 7);
v_offsetCnstrs_671_ = lean_ctor_get_uint8(v___x_662_, 8);
v_etaStruct_672_ = lean_ctor_get_uint8(v___x_662_, 10);
v_univApprox_673_ = lean_ctor_get_uint8(v___x_662_, 11);
v_iota_674_ = lean_ctor_get_uint8(v___x_662_, 12);
v_beta_675_ = lean_ctor_get_uint8(v___x_662_, 13);
v_proj_676_ = lean_ctor_get_uint8(v___x_662_, 14);
v_zeta_677_ = lean_ctor_get_uint8(v___x_662_, 15);
v_zetaDelta_678_ = lean_ctor_get_uint8(v___x_662_, 16);
v_zetaUnused_679_ = lean_ctor_get_uint8(v___x_662_, 17);
v_zetaHave_680_ = lean_ctor_get_uint8(v___x_662_, 18);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_726_ == 0)
{
v___x_682_ = v___x_662_;
v_isShared_683_ = v_isSharedCheck_726_;
goto v_resetjp_681_;
}
else
{
lean_dec(v___x_662_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_726_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v_trackZetaDelta_684_; lean_object* v_zetaDeltaSet_685_; lean_object* v_lctx_686_; lean_object* v_localInstances_687_; lean_object* v_defEqCtx_x3f_688_; lean_object* v_synthPendingDepth_689_; lean_object* v_canUnfold_x3f_690_; uint8_t v_univApprox_691_; uint8_t v_inTypeClassResolution_692_; uint8_t v_cacheInferType_693_; lean_object* v_config_695_; 
v_trackZetaDelta_684_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*7);
v_zetaDeltaSet_685_ = lean_ctor_get(v_a_655_, 1);
v_lctx_686_ = lean_ctor_get(v_a_655_, 2);
v_localInstances_687_ = lean_ctor_get(v_a_655_, 3);
v_defEqCtx_x3f_688_ = lean_ctor_get(v_a_655_, 4);
v_synthPendingDepth_689_ = lean_ctor_get(v_a_655_, 5);
v_canUnfold_x3f_690_ = lean_ctor_get(v_a_655_, 6);
v_univApprox_691_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_692_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*7 + 2);
v_cacheInferType_693_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*7 + 3);
if (v_isShared_683_ == 0)
{
v_config_695_ = v___x_682_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 0, v_foApprox_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 1, v_ctxApprox_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 2, v_quasiPatternApprox_665_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 3, v_constApprox_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 4, v_isDefEqStuckEx_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 5, v_unificationHints_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 6, v_proofIrrelevance_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 7, v_assignSyntheticOpaque_670_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 8, v_offsetCnstrs_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 10, v_etaStruct_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 11, v_univApprox_673_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 12, v_iota_674_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 13, v_beta_675_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 14, v_proj_676_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 15, v_zeta_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 16, v_zetaDelta_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 17, v_zetaUnused_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, 18, v_zetaHave_680_);
v_config_695_ = v_reuseFailAlloc_725_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v_key_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_ctor_set_uint8(v_config_695_, 9, v___y_661_);
v___x_696_ = l_Lean_Meta_Context_configKey(v_a_655_);
v___x_697_ = 2ULL;
v___x_698_ = lean_uint64_shift_right(v___x_696_, v___x_697_);
v___x_699_ = lean_uint64_shift_left(v___x_698_, v___x_697_);
v___x_700_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_661_);
v_key_701_ = lean_uint64_lor(v___x_699_, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_702_, 0, v_config_695_);
lean_ctor_set_uint64(v___x_702_, sizeof(void*)*1, v_key_701_);
lean_inc(v_canUnfold_x3f_690_);
lean_inc(v_synthPendingDepth_689_);
lean_inc(v_defEqCtx_x3f_688_);
lean_inc_ref(v_localInstances_687_);
lean_inc_ref(v_lctx_686_);
lean_inc(v_zetaDeltaSet_685_);
v___x_703_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_zetaDeltaSet_685_);
lean_ctor_set(v___x_703_, 2, v_lctx_686_);
lean_ctor_set(v___x_703_, 3, v_localInstances_687_);
lean_ctor_set(v___x_703_, 4, v_defEqCtx_x3f_688_);
lean_ctor_set(v___x_703_, 5, v_synthPendingDepth_689_);
lean_ctor_set(v___x_703_, 6, v_canUnfold_x3f_690_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*7, v_trackZetaDelta_684_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*7 + 1, v_univApprox_691_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*7 + 2, v_inTypeClassResolution_692_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*7 + 3, v_cacheInferType_693_);
lean_inc(v_a_658_);
lean_inc_ref(v_a_657_);
lean_inc(v_a_656_);
lean_inc_ref(v___x_703_);
lean_inc_ref(v_e_654_);
v___x_704_ = lean_whnf(v_e_654_, v___x_703_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_716_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_716_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
if (lean_obj_tag(v_a_705_) == 9)
{
lean_object* v_a_709_; 
v_a_709_ = lean_ctor_get(v_a_705_, 0);
lean_inc_ref(v_a_709_);
lean_dec_ref(v_a_705_);
if (lean_obj_tag(v_a_709_) == 1)
{
lean_object* v_val_710_; lean_object* v___x_712_; 
lean_dec_ref(v___x_703_);
lean_dec_ref(v_e_654_);
v_val_710_ = lean_ctor_get(v_a_709_, 0);
lean_inc_ref(v_val_710_);
lean_dec_ref(v_a_709_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_val_710_);
v___x_712_ = v___x_707_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_val_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___x_714_; 
lean_dec_ref(v_a_709_);
lean_del_object(v___x_707_);
v___x_714_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_654_, v___x_703_, v_a_656_, v_a_657_, v_a_658_);
lean_dec_ref(v___x_703_);
return v___x_714_;
}
}
else
{
lean_object* v___x_715_; 
lean_del_object(v___x_707_);
lean_dec(v_a_705_);
v___x_715_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_654_, v___x_703_, v_a_656_, v_a_657_, v_a_658_);
lean_dec_ref(v___x_703_);
return v___x_715_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v___x_703_);
lean_dec_ref(v_e_654_);
v_a_717_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_704_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_704_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object* v_e_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object* v___x_738_, lean_object* v_00___739_){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(2u);
v___x_741_ = lean_nat_dec_eq(v___x_738_, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object* v___x_742_, lean_object* v_00___743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_742_, v_00___743_);
lean_dec(v___x_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* v_e_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
lean_inc(v_a_767_);
lean_inc_ref(v_a_766_);
lean_inc(v_a_765_);
lean_inc_ref(v_a_764_);
v___x_769_ = lean_whnf(v_e_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_851_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_851_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_851_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_851_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Expr_getAppFn(v_a_770_);
if (lean_obj_tag(v___x_774_) == 4)
{
lean_object* v_declName_775_; lean_object* v___x_776_; uint8_t v___y_778_; uint8_t v___y_806_; uint8_t v___y_837_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_declName_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_declName_775_);
lean_dec_ref(v___x_774_);
v___x_776_ = l_Lean_Expr_getAppNumArgs(v_a_770_);
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7));
v___x_847_ = lean_name_eq(v_declName_775_, v___x_846_);
if (v___x_847_ == 0)
{
v___y_837_ = v___x_847_;
goto v___jp_836_;
}
else
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v___x_776_, v___x_848_);
v___y_837_ = v___x_849_;
goto v___jp_836_;
}
v___jp_777_:
{
if (v___y_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v___x_776_);
v___x_779_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_770_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_sub(v___x_776_, v___x_780_);
lean_dec(v___x_776_);
lean_inc(v___x_781_);
v___x_782_ = l_Lean_Expr_getRevArg_x21(v_a_770_, v___x_781_);
v___x_783_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_782_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_nat_sub(v___x_781_, v___x_780_);
lean_dec(v___x_781_);
v___x_786_ = l_Lean_Expr_getRevArg_x21(v_a_770_, v___x_785_);
lean_dec(v_a_770_);
v___x_787_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_786_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_Name_num___override(v_a_784_, v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_a_784_);
v_a_797_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_787_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_787_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_dec(v___x_781_);
lean_dec(v_a_770_);
return v___x_783_;
}
}
}
v___jp_805_:
{
if (v___y_806_ == 0)
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3));
v___x_808_ = lean_name_eq(v_declName_775_, v___x_807_);
lean_dec(v_declName_775_);
if (v___x_808_ == 0)
{
v___y_778_ = v___x_808_;
goto v___jp_777_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_box(0);
v___x_810_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_776_, v___x_809_);
v___y_778_ = v___x_810_;
goto v___jp_777_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_declName_775_);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_sub(v___x_776_, v___x_811_);
lean_dec(v___x_776_);
lean_inc(v___x_812_);
v___x_813_ = l_Lean_Expr_getRevArg_x21(v_a_770_, v___x_812_);
v___x_814_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v___x_813_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = lean_nat_sub(v___x_812_, v___x_811_);
lean_dec(v___x_812_);
v___x_817_ = l_Lean_Expr_getRevArg_x21(v_a_770_, v___x_816_);
lean_dec(v_a_770_);
v___x_818_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_817_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_Name_str___override(v_a_815_, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_a_815_);
v_a_828_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_818_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_818_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_dec(v___x_812_);
lean_dec(v_a_770_);
return v___x_814_;
}
}
}
v___jp_836_:
{
if (v___y_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
lean_del_object(v___x_772_);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5));
v___x_839_ = lean_name_eq(v_declName_775_, v___x_838_);
if (v___x_839_ == 0)
{
v___y_806_ = v___x_839_;
goto v___jp_805_;
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = lean_box(0);
v___x_841_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_776_, v___x_840_);
v___y_806_ = v___x_841_;
goto v___jp_805_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_dec(v___x_776_);
lean_dec(v_declName_775_);
lean_dec(v_a_770_);
v___x_842_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_842_);
v___x_844_ = v___x_772_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v___x_850_; 
lean_dec_ref(v___x_774_);
lean_del_object(v___x_772_);
v___x_850_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_770_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_850_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_769_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_769_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(lean_object* v_e_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1(lean_object* v_e_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName___private__1___boxed(lean_object* v_e_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Meta_instReduceEvalName___private__1(v_e_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(lean_object* v_inst_886_, lean_object* v_e_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; 
lean_inc(v_a_891_);
lean_inc_ref(v_a_890_);
lean_inc(v_a_889_);
lean_inc_ref(v_a_888_);
v___x_893_ = lean_whnf(v_e_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_955_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_955_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_955_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_955_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Expr_getAppFn(v_a_894_);
if (lean_obj_tag(v___x_898_) == 4)
{
lean_object* v_declName_899_; 
v_declName_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_declName_899_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v_declName_899_) == 1)
{
lean_object* v_pre_900_; 
v_pre_900_ = lean_ctor_get(v_declName_899_, 0);
lean_inc(v_pre_900_);
if (lean_obj_tag(v_pre_900_) == 1)
{
lean_object* v_pre_901_; 
v_pre_901_ = lean_ctor_get(v_pre_900_, 0);
if (lean_obj_tag(v_pre_901_) == 0)
{
lean_object* v_str_902_; lean_object* v_str_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_str_902_ = lean_ctor_get(v_declName_899_, 1);
lean_inc_ref(v_str_902_);
lean_dec_ref(v_declName_899_);
v_str_903_ = lean_ctor_get(v_pre_900_, 1);
lean_inc_ref(v_str_903_);
lean_dec_ref(v_pre_900_);
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0));
v___x_905_ = lean_string_dec_eq(v_str_903_, v___x_904_);
lean_dec_ref(v_str_903_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v_str_902_);
lean_del_object(v___x_896_);
lean_dec_ref(v_inst_886_);
v___x_906_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_907_ = l_Lean_Expr_getAppNumArgs(v_a_894_);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1));
v___x_909_ = lean_string_dec_eq(v_str_902_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; uint8_t v___x_911_; 
lean_del_object(v___x_896_);
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2));
v___x_911_ = lean_string_dec_eq(v_str_902_, v___x_910_);
lean_dec_ref(v_str_902_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_dec(v___x_907_);
lean_dec_ref(v_inst_886_);
v___x_912_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(3u);
v___x_914_ = lean_nat_dec_eq(v___x_907_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v___x_907_);
lean_dec_ref(v_inst_886_);
v___x_915_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_sub(v___x_907_, v___x_916_);
v___x_918_ = lean_nat_sub(v___x_917_, v___x_916_);
lean_dec(v___x_917_);
v___x_919_ = l_Lean_Expr_getRevArg_x21(v_a_894_, v___x_918_);
lean_inc_ref(v_inst_886_);
v___x_920_ = l_Lean_Meta_reduceEval___redArg(v_inst_886_, v___x_919_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = lean_unsigned_to_nat(2u);
v___x_923_ = lean_nat_sub(v___x_907_, v___x_922_);
lean_dec(v___x_907_);
v___x_924_ = lean_nat_sub(v___x_923_, v___x_916_);
lean_dec(v___x_923_);
v___x_925_ = l_Lean_Expr_getRevArg_x21(v_a_894_, v___x_924_);
lean_dec(v_a_894_);
v___x_926_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_886_, v___x_925_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_931_, 0, v_a_921_);
lean_ctor_set(v___x_931_, 1, v_a_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_dec(v_a_921_);
return v___x_926_;
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v___x_907_);
lean_dec(v_a_894_);
lean_dec_ref(v_inst_886_);
v_a_936_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_920_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_920_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; 
lean_dec_ref(v_str_902_);
lean_dec_ref(v_inst_886_);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_dec_eq(v___x_907_, v___x_944_);
lean_dec(v___x_907_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
lean_del_object(v___x_896_);
v___x_946_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec(v_a_894_);
v___x_947_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_947_);
v___x_949_ = v___x_896_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
lean_object* v___x_951_; 
lean_dec_ref(v_pre_900_);
lean_dec_ref(v_declName_899_);
lean_del_object(v___x_896_);
lean_dec_ref(v_inst_886_);
v___x_951_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_951_;
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v_pre_900_);
lean_dec_ref(v_declName_899_);
lean_del_object(v___x_896_);
lean_dec_ref(v_inst_886_);
v___x_952_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_952_;
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v_declName_899_);
lean_del_object(v___x_896_);
lean_dec_ref(v_inst_886_);
v___x_953_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_953_;
}
}
else
{
lean_object* v___x_954_; 
lean_dec_ref(v___x_898_);
lean_del_object(v___x_896_);
lean_dec_ref(v_inst_886_);
v___x_954_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_954_;
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_inst_886_);
v_a_956_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_893_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_893_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(lean_object* v_inst_964_, lean_object* v_e_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_964_, v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(lean_object* v_00_u03b1_972_, lean_object* v_inst_973_, lean_object* v_e_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_973_, v_e_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(lean_object* v_00_u03b1_981_, lean_object* v_inst_982_, lean_object* v_e_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(v_00_u03b1_981_, v_inst_982_, v_e_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg(lean_object* v_inst_990_, lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_990_, v_e_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(lean_object* v_inst_998_, lean_object* v_e_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(v_inst_998_, v_e_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1(lean_object* v_00_u03b1_1006_, lean_object* v_inst_1007_, lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_1007_, v_e_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___private__1___boxed(lean_object* v_00_u03b1_1015_, lean_object* v_inst_1016_, lean_object* v_e_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_instReduceEvalList___private__1(v_00_u03b1_1015_, v_inst_1016_, v_e_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList___redArg(lean_object* v_inst_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_1025_, 0, lean_box(0));
lean_closure_set(v___x_1025_, 1, v_inst_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalList(lean_object* v_00_u03b1_1026_, lean_object* v_inst_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalList___private__1___boxed), 8, 2);
lean_closure_set(v___x_1028_, 0, lean_box(0));
lean_closure_set(v___x_1028_, 1, v_inst_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(lean_object* v_n_1034_, lean_object* v_e_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
lean_inc(v_a_1039_);
lean_inc_ref(v_a_1038_);
lean_inc(v_a_1037_);
lean_inc_ref(v_a_1036_);
v___x_1041_ = lean_whnf(v_e_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1044_ = lean_unsigned_to_nat(3u);
v___x_1045_ = l_Lean_Expr_isAppOfArity(v_a_1042_, v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1042_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1046_;
}
else
{
lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___f_1047_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = l_Lean_Expr_getAppNumArgs(v_a_1042_);
v___x_1050_ = lean_nat_sub(v___x_1049_, v___x_1048_);
lean_dec(v___x_1049_);
v___x_1051_ = lean_nat_sub(v___x_1050_, v___x_1048_);
lean_dec(v___x_1050_);
v___x_1052_ = l_Lean_Expr_getRevArg_x21(v_a_1042_, v___x_1051_);
lean_dec(v_a_1042_);
v___x_1053_ = l_Lean_Meta_reduceEval___redArg(v___f_1047_, v___x_1052_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1062_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = lean_nat_mod(v_a_1054_, v_n_1034_);
lean_dec(v_a_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1053_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1053_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1041_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1041_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(lean_object* v_n_1079_, lean_object* v_e_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(v_n_1079_, v_e_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_n_1079_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(lean_object* v_n_1087_, lean_object* v_inst_1088_, lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; 
lean_inc(v_a_1093_);
lean_inc_ref(v_a_1092_);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
v___x_1095_ = lean_whnf(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2));
v___x_1098_ = lean_unsigned_to_nat(3u);
v___x_1099_ = l_Lean_Expr_isAppOfArity(v_a_1096_, v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1096_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1100_;
}
else
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___f_1101_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = l_Lean_Expr_getAppNumArgs(v_a_1096_);
v___x_1104_ = lean_nat_sub(v___x_1103_, v___x_1102_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_nat_sub(v___x_1104_, v___x_1102_);
lean_dec(v___x_1104_);
v___x_1106_ = l_Lean_Expr_getRevArg_x21(v_a_1096_, v___x_1105_);
lean_dec(v_a_1096_);
v___x_1107_ = l_Lean_Meta_reduceEval___redArg(v___f_1101_, v___x_1106_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_nat_mod(v_a_1108_, v_n_1087_);
lean_dec(v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1107_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1107_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1095_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1095_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(lean_object* v_n_1133_, lean_object* v_inst_1134_, lean_object* v_e_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(v_n_1133_, v_inst_1134_, v_e_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_n_1133_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(lean_object* v_n_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1143_, 0, v_n_1142_);
lean_closure_set(v___x_1143_, 1, lean_box(0));
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFinOfNeZeroNat(lean_object* v_n_1144_, lean_object* v_inst_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1146_, 0, v_n_1144_);
lean_closure_set(v___x_1146_, 1, lean_box(0));
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1(lean_object* v_n_1152_, lean_object* v_e_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; 
lean_inc(v_a_1157_);
lean_inc_ref(v_a_1156_);
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
v___x_1159_ = lean_whnf(v_e_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2));
v___x_1162_ = lean_unsigned_to_nat(2u);
v___x_1163_ = l_Lean_Expr_isAppOfArity(v_a_1160_, v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1160_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1165_ = lean_nat_pow(v___x_1162_, v_n_1152_);
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_nat_sub(v___x_1165_, v___x_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_nat_add(v___x_1167_, v___x_1166_);
lean_dec(v___x_1167_);
v___x_1169_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed), 8, 2);
lean_closure_set(v___x_1169_, 0, v___x_1168_);
lean_closure_set(v___x_1169_, 1, lean_box(0));
v___x_1170_ = l_Lean_Expr_getAppNumArgs(v_a_1160_);
v___x_1171_ = lean_nat_sub(v___x_1170_, v___x_1166_);
lean_dec(v___x_1170_);
v___x_1172_ = lean_nat_sub(v___x_1171_, v___x_1166_);
lean_dec(v___x_1171_);
v___x_1173_ = l_Lean_Expr_getRevArg_x21(v_a_1160_, v___x_1172_);
lean_dec(v_a_1160_);
v___x_1174_ = l_Lean_Meta_reduceEval___redArg(v___x_1169_, v___x_1173_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
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
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1174_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1174_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1159_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1159_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(lean_object* v_n_1199_, lean_object* v_e_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_instReduceEvalBitVec___private__1(v_n_1199_, v_e_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_n_1199_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBitVec(lean_object* v_n_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalBitVec___private__1___boxed), 7, 1);
lean_closure_set(v___x_1208_, 0, v_n_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1(lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
lean_inc(v_a_1222_);
lean_inc_ref(v_a_1221_);
lean_inc(v_a_1220_);
lean_inc_ref(v_a_1219_);
v___x_1224_ = lean_whnf(v_e_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1242_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1242_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1242_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__2));
v___x_1230_ = l_Lean_Expr_isAppOf(v_a_1225_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBool___private__1___closed__4));
v___x_1232_ = l_Lean_Expr_isAppOf(v_a_1225_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_del_object(v___x_1227_);
v___x_1233_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1225_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec(v_a_1225_);
v___x_1234_ = lean_box(v___x_1230_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1234_);
v___x_1236_ = v___x_1227_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
lean_dec(v_a_1225_);
v___x_1238_ = lean_box(v___x_1230_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1238_);
v___x_1240_ = v___x_1227_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_a_1243_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1224_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1224_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBool___private__1___boxed(lean_object* v_e_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Meta_instReduceEvalBool___private__1(v_e_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1(lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; 
lean_inc(v_a_1269_);
lean_inc_ref(v_a_1268_);
lean_inc(v_a_1267_);
lean_inc_ref(v_a_1266_);
lean_inc_ref(v_e_1265_);
v___x_1271_ = lean_whnf(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1324_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1324_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1324_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Expr_constName_x3f(v_a_1272_);
lean_dec(v_a_1272_);
if (lean_obj_tag(v___x_1276_) == 1)
{
lean_object* v_val_1277_; 
v_val_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v___x_1276_);
if (lean_obj_tag(v_val_1277_) == 1)
{
lean_object* v_pre_1278_; 
v_pre_1278_ = lean_ctor_get(v_val_1277_, 0);
lean_inc(v_pre_1278_);
if (lean_obj_tag(v_pre_1278_) == 1)
{
lean_object* v_pre_1279_; 
v_pre_1279_ = lean_ctor_get(v_pre_1278_, 0);
lean_inc(v_pre_1279_);
if (lean_obj_tag(v_pre_1279_) == 1)
{
lean_object* v_pre_1280_; 
v_pre_1280_ = lean_ctor_get(v_pre_1279_, 0);
if (lean_obj_tag(v_pre_1280_) == 0)
{
lean_object* v_str_1281_; lean_object* v_str_1282_; lean_object* v_str_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_str_1281_ = lean_ctor_get(v_val_1277_, 1);
lean_inc_ref(v_str_1281_);
lean_dec_ref(v_val_1277_);
v_str_1282_ = lean_ctor_get(v_pre_1278_, 1);
lean_inc_ref(v_str_1282_);
lean_dec_ref(v_pre_1278_);
v_str_1283_ = lean_ctor_get(v_pre_1279_, 1);
lean_inc_ref(v_str_1283_);
lean_dec_ref(v_pre_1279_);
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0));
v___x_1285_ = lean_string_dec_eq(v_str_1283_, v___x_1284_);
lean_dec_ref(v_str_1283_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref(v_str_1282_);
lean_dec_ref(v_str_1281_);
lean_del_object(v___x_1274_);
v___x_1286_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0));
v___x_1288_ = lean_string_dec_eq(v_str_1282_, v___x_1287_);
lean_dec_ref(v_str_1282_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v_str_1281_);
lean_del_object(v___x_1274_);
v___x_1289_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1));
v___x_1291_ = lean_string_dec_eq(v_str_1281_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2));
v___x_1293_ = lean_string_dec_eq(v_str_1281_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3));
v___x_1295_ = lean_string_dec_eq(v_str_1281_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4));
v___x_1297_ = lean_string_dec_eq(v_str_1281_, v___x_1296_);
lean_dec_ref(v_str_1281_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
lean_del_object(v___x_1274_);
v___x_1298_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1298_;
}
else
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec_ref(v_e_1265_);
v___x_1299_ = 3;
v___x_1300_ = lean_box(v___x_1299_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1300_);
v___x_1302_ = v___x_1274_;
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
lean_dec_ref(v_str_1281_);
lean_dec_ref(v_e_1265_);
v___x_1304_ = 2;
v___x_1305_ = lean_box(v___x_1304_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1305_);
v___x_1307_ = v___x_1274_;
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
uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
lean_dec_ref(v_str_1281_);
lean_dec_ref(v_e_1265_);
v___x_1309_ = 1;
v___x_1310_ = lean_box(v___x_1309_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1310_);
v___x_1312_ = v___x_1274_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_dec_ref(v_str_1281_);
lean_dec_ref(v_e_1265_);
v___x_1314_ = 0;
v___x_1315_ = lean_box(v___x_1314_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1315_);
v___x_1317_ = v___x_1274_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_object* v___x_1319_; 
lean_dec_ref(v_pre_1279_);
lean_dec_ref(v_pre_1278_);
lean_dec_ref(v_val_1277_);
lean_del_object(v___x_1274_);
v___x_1319_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1319_;
}
}
else
{
lean_object* v___x_1320_; 
lean_dec_ref(v_pre_1278_);
lean_dec(v_pre_1279_);
lean_dec_ref(v_val_1277_);
lean_del_object(v___x_1274_);
v___x_1320_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1320_;
}
}
else
{
lean_object* v___x_1321_; 
lean_dec_ref(v_val_1277_);
lean_dec(v_pre_1278_);
lean_del_object(v___x_1274_);
v___x_1321_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1321_;
}
}
else
{
lean_object* v___x_1322_; 
lean_dec(v_val_1277_);
lean_del_object(v___x_1274_);
v___x_1322_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1322_;
}
}
else
{
lean_object* v___x_1323_; 
lean_dec(v___x_1276_);
lean_del_object(v___x_1274_);
v___x_1323_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_e_1265_);
v_a_1325_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1271_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1271_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(lean_object* v_e_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(v_e_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1(lean_object* v_e_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; 
lean_inc(v_a_1357_);
lean_inc_ref(v_a_1356_);
lean_inc(v_a_1355_);
lean_inc_ref(v_a_1354_);
v___x_1359_ = lean_whnf(v_e_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2));
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = l_Lean_Expr_isAppOfArity(v_a_1360_, v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4));
v___x_1365_ = l_Lean_Expr_isAppOfArity(v_a_1360_, v___x_1364_, v___x_1362_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1360_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
return v___x_1366_;
}
else
{
lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___f_1367_ = ((lean_object*)(l_Lean_Meta_instReduceEvalString___closed__0));
v___x_1368_ = l_Lean_Expr_getAppNumArgs(v_a_1360_);
v___x_1369_ = lean_nat_sub(v___x_1368_, v___x_1362_);
lean_dec(v___x_1368_);
v___x_1370_ = l_Lean_Expr_getRevArg_x21(v_a_1360_, v___x_1369_);
lean_dec(v_a_1360_);
v___x_1371_ = l_Lean_Meta_reduceEval___redArg(v___f_1367_, v___x_1370_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_a_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1371_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1371_);
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
else
{
lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___f_1389_ = ((lean_object*)(l_Lean_Meta_instReduceEvalNat___closed__0));
v___x_1390_ = l_Lean_Expr_getAppNumArgs(v_a_1360_);
v___x_1391_ = lean_nat_sub(v___x_1390_, v___x_1362_);
lean_dec(v___x_1390_);
v___x_1392_ = l_Lean_Expr_getRevArg_x21(v_a_1360_, v___x_1391_);
lean_dec(v_a_1360_);
v___x_1393_ = l_Lean_Meta_reduceEval___redArg(v___f_1389_, v___x_1392_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
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
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1359_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1359_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(lean_object* v_e_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_instReduceEvalLiteral___private__1(v_e_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1(lean_object* v_e_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1439_; 
lean_inc(v_a_1437_);
lean_inc_ref(v_a_1436_);
lean_inc(v_a_1435_);
lean_inc_ref(v_a_1434_);
v___x_1439_ = lean_whnf(v_e_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = l_Lean_Expr_isAppOfArity(v_a_1440_, v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1440_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
return v___x_1444_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1445_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1446_ = l_Lean_Expr_getAppNumArgs(v_a_1440_);
v___x_1447_ = lean_nat_sub(v___x_1446_, v___x_1442_);
lean_dec(v___x_1446_);
v___x_1448_ = l_Lean_Expr_getRevArg_x21(v_a_1440_, v___x_1447_);
lean_dec(v_a_1440_);
v___x_1449_ = l_Lean_Meta_reduceEval___redArg(v___x_1445_, v___x_1448_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1449_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1449_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1439_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1439_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(lean_object* v_e_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Meta_instReduceEvalMVarId___private__1(v_e_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0(lean_object* v_e_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
v___x_1487_ = lean_whnf(v_e_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1));
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = l_Lean_Expr_isAppOfArity(v_a_1488_, v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
v___x_1492_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1488_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1494_ = l_Lean_Expr_getAppNumArgs(v_a_1488_);
v___x_1495_ = lean_nat_sub(v___x_1494_, v___x_1490_);
lean_dec(v___x_1494_);
v___x_1496_ = l_Lean_Expr_getRevArg_x21(v_a_1488_, v___x_1495_);
lean_dec(v_a_1488_);
v___x_1497_ = l_Lean_Meta_reduceEval___redArg(v___x_1493_, v___x_1496_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
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
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_a_1506_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1497_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1497_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
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
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1487_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1487_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed(lean_object* v_e_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(v_e_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1(lean_object* v_e_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; 
lean_inc(v_a_1540_);
lean_inc_ref(v_a_1539_);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
v___x_1542_ = lean_whnf(v_e_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = l_Lean_Expr_isAppOfArity(v_a_1543_, v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1543_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1548_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1549_ = l_Lean_Expr_getAppNumArgs(v_a_1543_);
v___x_1550_ = lean_nat_sub(v___x_1549_, v___x_1545_);
lean_dec(v___x_1549_);
v___x_1551_ = l_Lean_Expr_getRevArg_x21(v_a_1543_, v___x_1550_);
lean_dec(v_a_1543_);
v___x_1552_ = l_Lean_Meta_reduceEval___redArg(v___x_1548_, v___x_1551_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1552_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1552_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1542_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1542_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(lean_object* v_e_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(v_e_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(lean_object* v_e_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
v___x_1590_ = lean_whnf(v_e_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = ((lean_object*)(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1));
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = l_Lean_Expr_isAppOfArity(v_a_1591_, v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1591_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1596_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1597_ = l_Lean_Expr_getAppNumArgs(v_a_1591_);
v___x_1598_ = lean_nat_sub(v___x_1597_, v___x_1593_);
lean_dec(v___x_1597_);
v___x_1599_ = l_Lean_Expr_getRevArg_x21(v_a_1591_, v___x_1598_);
lean_dec(v_a_1591_);
v___x_1600_ = l_Lean_Meta_reduceEval___redArg(v___x_1596_, v___x_1599_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1600_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1600_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1590_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1590_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed(lean_object* v_e_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(v_e_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1(lean_object* v_e_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1645_; 
lean_inc(v_a_1643_);
lean_inc_ref(v_a_1642_);
lean_inc(v_a_1641_);
lean_inc_ref(v_a_1640_);
v___x_1645_ = lean_whnf(v_e_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = l_Lean_Expr_isAppOfArity(v_a_1646_, v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1646_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1652_ = l_Lean_Expr_getAppNumArgs(v_a_1646_);
v___x_1653_ = lean_nat_sub(v___x_1652_, v___x_1648_);
lean_dec(v___x_1652_);
v___x_1654_ = l_Lean_Expr_getRevArg_x21(v_a_1646_, v___x_1653_);
lean_dec(v_a_1646_);
v___x_1655_ = l_Lean_Meta_reduceEval___redArg(v___x_1651_, v___x_1654_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1655_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1655_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_a_1672_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1645_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1645_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(lean_object* v_e_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Meta_instReduceEvalFVarId___private__1(v_e_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0(lean_object* v_e_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
v___x_1693_ = lean_whnf(v_e_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = ((lean_object*)(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1));
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = l_Lean_Expr_isAppOfArity(v_a_1694_, v___x_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_1694_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1699_ = ((lean_object*)(l_Lean_Meta_instReduceEvalName___closed__0));
v___x_1700_ = l_Lean_Expr_getAppNumArgs(v_a_1694_);
v___x_1701_ = lean_nat_sub(v___x_1700_, v___x_1696_);
lean_dec(v___x_1700_);
v___x_1702_ = l_Lean_Expr_getRevArg_x21(v_a_1694_, v___x_1701_);
lean_dec(v_a_1694_);
v___x_1703_ = l_Lean_Meta_reduceEval___redArg(v___x_1699_, v___x_1702_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1703_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1703_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1693_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1693_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed(lean_object* v_e_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(v_e_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1734_;
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
