// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs
// Imports: import Init.Simproc public import Lean.Meta.Tactic.Simp.Simproc import Lean.Meta.MethodSpecs import Lean.Meta.Tactic.Simp.Main
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_getMethodSpecTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkSimpTheoremFromConst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_instInhabitedSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorem_default;
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedSimpM___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs.0.reduceMethod"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: simpThms.size = 1\n    "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_reduceBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_reduceBEq___closed__0 = (const lean_object*)&l_reduceBEq___closed__0_value;
static const lean_string_object l_reduceBEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_reduceBEq___closed__1 = (const lean_object*)&l_reduceBEq___closed__1_value;
static const lean_ctor_object l_reduceBEq___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceBEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_reduceBEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_reduceBEq___closed__2_value_aux_0),((lean_object*)&l_reduceBEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_reduceBEq___closed__2 = (const lean_object*)&l_reduceBEq___closed__2_value;
LEAN_EXPORT lean_object* l_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(7, 43, 34, 163, 80, 156, 84, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceBEq___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13____boxed(lean_object*);
static const lean_string_object l_reduceOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ord"};
static const lean_object* l_reduceOrd___closed__0 = (const lean_object*)&l_reduceOrd___closed__0_value;
static const lean_string_object l_reduceOrd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_reduceOrd___closed__1 = (const lean_object*)&l_reduceOrd___closed__1_value;
static const lean_ctor_object l_reduceOrd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceOrd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 34, 14, 190, 177, 218, 16, 31)}};
static const lean_ctor_object l_reduceOrd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_reduceOrd___closed__2_value_aux_0),((lean_object*)&l_reduceOrd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(241, 180, 168, 39, 68, 69, 153, 110)}};
static const lean_object* l_reduceOrd___closed__2 = (const lean_object*)&l_reduceOrd___closed__2_value;
LEAN_EXPORT lean_object* l_reduceOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceOrd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(214, 237, 65, 80, 201, 127, 149, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceOrd___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_8504__overap_12_; lean_object* v___x_13_; 
v___f_11_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0));
v___x_8504__overap_12_ = lean_panic_fn_borrowed(v___f_11_, v_msg_2_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
v___x_13_ = lean_apply_8(v___x_8504__overap_12_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___boxed(lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v_msg_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
return v_res_23_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_27_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2));
v___x_28_ = lean_unsigned_to_nat(4u);
v___x_29_ = lean_unsigned_to_nat(28u);
v___x_30_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1));
v___x_31_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0));
v___x_32_ = l_mkPanicMessageWithDecl(v___x_31_, v___x_30_, v___x_29_, v___x_28_, v___x_27_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(uint8_t v___x_36_, lean_object* v_e_37_, lean_object* v_as_38_, size_t v_sz_39_, size_t v_i_40_, lean_object* v_b_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_a_51_; uint8_t v___x_55_; 
v___x_55_ = lean_usize_dec_lt(v_i_40_, v_sz_39_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; 
lean_dec_ref(v_e_37_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v_b_41_);
return v___x_56_;
}
else
{
lean_object* v_a_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec_ref(v_b_41_);
v_a_57_ = lean_array_uget_borrowed(v_as_38_, v_i_40_);
v___x_58_ = 0;
v___x_59_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_57_);
v___x_60_ = l_Lean_Meta_mkSimpTheoremFromConst(v_a_57_, v___x_36_, v___x_58_, v___x_59_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v___x_60_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_array_get_size(v_a_61_);
v___x_64_ = lean_nat_dec_eq(v___x_63_, v___x_62_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_a_61_);
v___x_65_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3);
v___x_66_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v___x_65_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_76_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_76_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_76_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_76_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
if (lean_obj_tag(v_a_67_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; 
lean_dec_ref(v_e_37_);
v_a_71_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_a_71_);
lean_dec_ref(v_a_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v_a_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
else
{
lean_object* v_a_75_; 
lean_del_object(v___x_69_);
v_a_75_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_a_75_);
lean_dec_ref(v_a_67_);
v_a_51_ = v_a_75_;
goto v___jp_50_;
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec_ref(v_e_37_);
v_a_77_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_66_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_66_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_Meta_instInhabitedSimpTheorem_default;
v___x_87_ = lean_array_get(v___x_86_, v_a_61_, v___x_85_);
lean_dec(v_a_61_);
lean_inc_ref(v_e_37_);
v___x_88_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_37_, v___x_87_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_108_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_108_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_108_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_108_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
if (lean_obj_tag(v_a_89_) == 1)
{
lean_object* v_val_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_106_; 
lean_dec_ref(v_e_37_);
v_val_94_ = lean_ctor_get(v_a_89_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_89_);
if (v_isSharedCheck_106_ == 0)
{
v___x_96_ = v_a_89_;
v_isShared_97_ = v_isSharedCheck_106_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_val_94_);
lean_dec(v_a_89_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_106_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_val_94_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_93_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_101_);
v___x_103_ = v___x_91_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
else
{
lean_object* v___x_107_; 
lean_del_object(v___x_91_);
lean_dec(v_a_89_);
v___x_107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4));
v_a_51_ = v___x_107_;
goto v___jp_50_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref(v_e_37_);
v_a_109_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_88_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_88_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v_e_37_);
v_a_117_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_60_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_60_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
v___jp_50_:
{
size_t v___x_52_; size_t v___x_53_; 
v___x_52_ = ((size_t)1ULL);
v___x_53_ = lean_usize_add(v_i_40_, v___x_52_);
v_i_40_ = v___x_53_;
v_b_41_ = v_a_51_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___boxed(lean_object* v___x_125_, lean_object* v_e_126_, lean_object* v_as_127_, lean_object* v_sz_128_, lean_object* v_i_129_, lean_object* v_b_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
uint8_t v___x_9322__boxed_139_; size_t v_sz_boxed_140_; size_t v_i_boxed_141_; lean_object* v_res_142_; 
v___x_9322__boxed_139_ = lean_unbox(v___x_125_);
v_sz_boxed_140_ = lean_unbox_usize(v_sz_128_);
lean_dec(v_sz_128_);
v_i_boxed_141_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_9322__boxed_139_, v_e_126_, v_as_127_, v_sz_boxed_140_, v_i_boxed_141_, v_b_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v_as_127_);
return v_res_142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0(void){
_start:
{
lean_object* v___x_143_; lean_object* v_dummy_144_; 
v___x_143_ = lean_box(0);
v_dummy_144_ = l_Lean_Expr_sort___override(v___x_143_);
return v_dummy_144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1(void){
_start:
{
lean_object* v_dummy_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_dummy_145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0);
v___x_146_ = lean_unsigned_to_nat(3u);
v___x_147_ = lean_mk_array(v___x_146_, v_dummy_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(lean_object* v_opName_152_, lean_object* v_e_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_xs_165_; lean_object* v___x_166_; lean_object* v_inst_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_162_ = l_Lean_instInhabitedExpr;
v___x_163_ = lean_unsigned_to_nat(3u);
v___x_164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1);
lean_inc_ref(v_e_153_);
v_xs_165_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v___x_163_, v_e_153_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(0u);
v_inst_167_ = lean_array_get(v___x_162_, v_xs_165_, v___x_166_);
v___x_168_ = l_Lean_Expr_getAppFn(v_inst_167_);
lean_dec(v_inst_167_);
v___x_169_ = l_Lean_Expr_isConst(v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec_ref(v___x_168_);
lean_dec_ref(v_xs_165_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_opName_152_);
v___x_170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v_lhs_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v_lhs_173_ = lean_array_get(v___x_162_, v_xs_165_, v___x_172_);
v___x_174_ = l_Lean_Meta_isConstructorApp_x3f(v_lhs_173_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_249_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_249_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_249_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_249_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
if (lean_obj_tag(v_a_175_) == 1)
{
lean_object* v___x_179_; lean_object* v_rhs_180_; lean_object* v___x_181_; 
lean_dec_ref(v_a_175_);
lean_del_object(v___x_177_);
v___x_179_ = lean_unsigned_to_nat(2u);
v_rhs_180_ = lean_array_get(v___x_162_, v_xs_165_, v___x_179_);
lean_dec_ref(v_xs_165_);
v___x_181_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_180_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_236_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_236_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_236_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_236_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
if (lean_obj_tag(v_a_182_) == 1)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec_ref(v_a_182_);
lean_del_object(v___x_184_);
v___x_186_ = l_Lean_Expr_constName_x21(v___x_168_);
lean_dec_ref(v___x_168_);
v___x_187_ = l_Lean_getMethodSpecTheorems(v___x_186_, v_opName_152_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_223_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_223_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_223_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_223_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
if (lean_obj_tag(v_a_188_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_193_; size_t v_sz_194_; size_t v___x_195_; lean_object* v___x_196_; 
lean_del_object(v___x_190_);
v_val_192_ = lean_ctor_get(v_a_188_, 0);
lean_inc(v_val_192_);
lean_dec_ref(v_a_188_);
v___x_193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4));
v_sz_194_ = lean_array_size(v_val_192_);
v___x_195_ = ((size_t)0ULL);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_169_, v_e_153_, v_val_192_, v_sz_194_, v___x_195_, v___x_193_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_val_192_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_210_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_210_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_fst_201_; 
v_fst_201_ = lean_ctor_get(v_a_197_, 0);
lean_inc(v_fst_201_);
lean_dec(v_a_197_);
if (lean_obj_tag(v_fst_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3));
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_204_ = v___x_199_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_object* v_val_206_; lean_object* v___x_208_; 
v_val_206_ = lean_ctor_get(v_fst_201_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v_fst_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v_val_206_);
v___x_208_ = v___x_199_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_val_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_196_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_196_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec(v_a_188_);
lean_dec_ref(v_e_153_);
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_219_);
v___x_221_ = v___x_190_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v_e_153_);
v_a_224_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_187_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_187_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v_a_182_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_opName_152_);
v___x_232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_232_);
v___x_234_ = v___x_184_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec_ref(v___x_168_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_opName_152_);
v_a_237_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_181_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_181_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec(v_a_175_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v_xs_165_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_opName_152_);
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_245_);
v___x_247_ = v___x_177_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v___x_168_);
lean_dec_ref(v_xs_165_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_opName_152_);
v_a_250_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_174_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_174_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___boxed(lean_object* v_opName_258_, lean_object* v_e_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v_opName_258_, v_e_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_reduceBEq(lean_object* v_e_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_283_ = ((lean_object*)(l_reduceBEq___closed__1));
v___x_284_ = ((lean_object*)(l_reduceBEq___closed__2));
v___x_285_ = lean_unsigned_to_nat(4u);
v___x_286_ = l_Lean_Expr_isAppOfArity(v_e_274_, v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec_ref(v_e_274_);
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v___x_283_, v_e_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_reduceBEq___boxed(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_reduceBEq(v_e_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_));
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_));
v___x_318_ = lean_alloc_closure((void*)(l_reduceBEq___boxed), 9, 0);
v___x_319_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_316_, v___x_317_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13____boxed(lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_reduceOrd(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = ((lean_object*)(l_reduceOrd___closed__1));
v___x_337_ = ((lean_object*)(l_reduceOrd___closed__2));
v___x_338_ = lean_unsigned_to_nat(4u);
v___x_339_ = l_Lean_Expr_isAppOfArity(v_e_327_, v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_e_327_);
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v___x_336_, v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_reduceOrd___boxed(lean_object* v_e_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_reduceOrd(v_e_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_));
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_));
v___x_371_ = lean_alloc_closure((void*)(l_reduceOrd___boxed), 9, 0);
v___x_372_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_369_, v___x_370_, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11____boxed(lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_();
return v_res_374_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MethodSpecs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MethodSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_MethodSpecs(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MethodSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
}
#ifdef __cplusplus
}
#endif
