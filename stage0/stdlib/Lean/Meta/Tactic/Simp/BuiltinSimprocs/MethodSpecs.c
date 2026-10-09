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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_getMethodSpecTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorem_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkSimpTheoremFromConst(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_instInhabitedSimpM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedSimpM___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs.0.reduceMethod"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: simpThms.size = 1\n    "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(7, 43, 34, 163, 80, 156, 84, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceBEq___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20____boxed(lean_object*);
static const lean_string_object l_reduceOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ord"};
static const lean_object* l_reduceOrd___closed__0 = (const lean_object*)&l_reduceOrd___closed__0_value;
static const lean_string_object l_reduceOrd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_reduceOrd___closed__1 = (const lean_object*)&l_reduceOrd___closed__1_value;
static const lean_ctor_object l_reduceOrd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceOrd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 34, 14, 190, 177, 218, 16, 31)}};
static const lean_ctor_object l_reduceOrd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_reduceOrd___closed__2_value_aux_0),((lean_object*)&l_reduceOrd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(241, 180, 168, 39, 68, 69, 153, 110)}};
static const lean_object* l_reduceOrd___closed__2 = (const lean_object*)&l_reduceOrd___closed__2_value;
LEAN_EXPORT lean_object* l_reduceOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceOrd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(214, 237, 65, 80, 201, 127, 149, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceOrd___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18____boxed(lean_object*);
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_7645__overap_12_; lean_object* v___x_13_; 
v___f_11_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0));
v___x_7645__overap_12_ = lean_panic_fn_borrowed(v___f_11_, v_msg_2_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
v___x_13_ = lean_apply_8(v___x_7645__overap_12_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v___y_7_ = stack[5].m_obj;
lean_object* v___y_8_ = stack[6].m_obj;
lean_object* v___y_9_ = stack[7].m_obj;
lean_object* v_res_14_;
v_res_14_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___boxed(lean_object* v_msg_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v_msg_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
return v_res_24_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_31_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3));
v___x_32_ = lean_unsigned_to_nat(4u);
v___x_33_ = lean_unsigned_to_nat(28u);
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2));
v___x_35_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1));
v___x_36_ = l_mkPanicMessageWithDecl(v___x_35_, v___x_34_, v___x_33_, v___x_32_, v___x_31_);
return v___x_36_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(uint8_t v___x_37_, lean_object* v_e_38_, lean_object* v_as_39_, size_t v_sz_40_, size_t v_i_41_, lean_object* v_b_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_a_52_; uint8_t v___x_56_; 
v___x_56_ = lean_usize_dec_lt(v_i_41_, v_sz_40_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v_e_38_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v_b_42_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_a_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref(v_b_42_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = l_Lean_Meta_instInhabitedSimpTheorem_default;
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_box(0);
v___x_62_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0));
v_a_63_ = lean_array_uget_borrowed(v_as_39_, v_i_41_);
v___x_64_ = 0;
v___x_65_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_63_);
v___x_66_ = l_Lean_Meta_mkSimpTheoremFromConst(v_a_63_, v___x_37_, v___x_64_, v___x_65_, v___x_64_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = lean_array_get_size(v_a_67_);
v___x_69_ = lean_nat_dec_eq(v___x_68_, v___x_58_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_a_67_);
v___x_70_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4);
v___x_71_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v___x_70_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_81_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_81_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_81_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_81_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
if (lean_obj_tag(v_a_72_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; 
lean_dec_ref(v_e_38_);
v_a_76_ = lean_ctor_get(v_a_72_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v_a_72_, 1);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v_a_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
else
{
lean_object* v_a_80_; 
lean_del_object(v___x_74_);
v_a_80_ = lean_ctor_get(v_a_72_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v_a_72_, 1);
v_a_52_ = v_a_80_;
goto v___jp_51_;
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec_ref(v_e_38_);
v_a_82_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_71_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_71_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_array_get(v___x_59_, v_a_67_, v___x_60_);
lean_dec(v_a_67_);
lean_inc_ref(v_e_38_);
v___x_91_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_38_, v___x_90_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_109_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_109_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_109_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_109_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
if (lean_obj_tag(v_a_92_) == 1)
{
lean_object* v_val_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_e_38_);
v_val_96_ = lean_ctor_get(v_a_92_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_a_92_);
if (v_isSharedCheck_108_ == 0)
{
v___x_98_ = v_a_92_;
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_val_96_);
lean_dec(v_a_92_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_val_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_107_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_61_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_103_);
v___x_105_ = v___x_94_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
else
{
lean_del_object(v___x_94_);
lean_dec(v_a_92_);
v_a_52_ = v___x_62_;
goto v___jp_51_;
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v_e_38_);
v_a_110_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_91_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_91_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_e_38_);
v_a_118_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_66_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_66_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
v___jp_51_:
{
size_t v___x_53_; size_t v___x_54_; 
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_add(v_i_41_, v___x_53_);
v_i_41_ = v___x_54_;
v_b_42_ = v_a_52_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_37_ = stack[0].m_num;
lean_object* v_e_38_ = stack[1].m_obj;
lean_object* v_as_39_ = stack[2].m_obj;
size_t v_sz_40_ = stack[3].m_num;
size_t v_i_41_ = stack[4].m_num;
lean_object* v_b_42_ = stack[5].m_obj;
lean_object* v___y_43_ = stack[6].m_obj;
lean_object* v___y_44_ = stack[7].m_obj;
lean_object* v___y_45_ = stack[8].m_obj;
lean_object* v___y_46_ = stack[9].m_obj;
lean_object* v___y_47_ = stack[10].m_obj;
lean_object* v___y_48_ = stack[11].m_obj;
lean_object* v___y_49_ = stack[12].m_obj;
lean_object* v_res_126_;
v_res_126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_37_, v_e_38_, v_as_39_, v_sz_40_, v_i_41_, v_b_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___boxed(lean_object* v___x_127_, lean_object* v_e_128_, lean_object* v_as_129_, lean_object* v_sz_130_, lean_object* v_i_131_, lean_object* v_b_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
uint8_t v___x_8482__boxed_141_; size_t v_sz_boxed_142_; size_t v_i_boxed_143_; lean_object* v_res_144_; 
v___x_8482__boxed_141_ = lean_unbox(v___x_127_);
v_sz_boxed_142_ = lean_unbox_usize(v_sz_130_);
lean_dec(v_sz_130_);
v_i_boxed_143_ = lean_unbox_usize(v_i_131_);
lean_dec(v_i_131_);
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_8482__boxed_141_, v_e_128_, v_as_129_, v_sz_boxed_142_, v_i_boxed_143_, v_b_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v_as_129_);
return v_res_144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v_dummy_146_; 
v___x_145_ = lean_box(0);
v_dummy_146_ = l_Lean_Expr_sort___override(v___x_145_);
return v_dummy_146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1(void){
_start:
{
lean_object* v_dummy_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_dummy_147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0);
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = lean_mk_array(v___x_148_, v_dummy_147_);
return v___x_149_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(lean_object* v_opName_154_, lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_xs_167_; lean_object* v___x_168_; lean_object* v_inst_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_164_ = l_Lean_instInhabitedExpr;
v___x_165_ = lean_unsigned_to_nat(3u);
v___x_166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1);
lean_inc_ref(v_e_155_);
v_xs_167_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v___x_165_, v_e_155_, v___x_166_);
v___x_168_ = lean_unsigned_to_nat(0u);
v_inst_169_ = lean_array_get_borrowed(v___x_164_, v_xs_167_, v___x_168_);
v___x_170_ = l_Lean_Expr_getAppFn(v_inst_169_);
v___x_171_ = l_Lean_Expr_isConst(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref(v___x_170_);
lean_dec_ref(v_xs_167_);
lean_dec_ref(v_e_155_);
lean_dec_ref(v_opName_154_);
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v_lhs_175_; lean_object* v___x_176_; lean_object* v_rhs_177_; lean_object* v___x_178_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v_lhs_175_ = lean_array_get(v___x_164_, v_xs_167_, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(2u);
v_rhs_177_ = lean_array_get(v___x_164_, v_xs_167_, v___x_176_);
lean_dec_ref(v_xs_167_);
v___x_178_ = l_Lean_Meta_isConstructorApp_x3f(v_lhs_175_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_251_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_251_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_251_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_251_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
if (lean_obj_tag(v_a_179_) == 1)
{
lean_object* v___x_183_; 
lean_dec_ref_known(v_a_179_, 1);
lean_del_object(v___x_181_);
v___x_183_ = l_Lean_Meta_isConstructorApp_x3f(v_rhs_177_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_238_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_238_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_238_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_238_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
if (lean_obj_tag(v_a_184_) == 1)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec_ref_known(v_a_184_, 1);
lean_del_object(v___x_186_);
v___x_188_ = l_Lean_Expr_constName_x21(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_189_ = l_Lean_getMethodSpecTheorems(v___x_188_, v_opName_154_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_225_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_225_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_225_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_225_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
if (lean_obj_tag(v_a_190_) == 1)
{
lean_object* v_val_194_; lean_object* v___x_195_; size_t v_sz_196_; size_t v___x_197_; lean_object* v___x_198_; 
lean_del_object(v___x_192_);
v_val_194_ = lean_ctor_get(v_a_190_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v_a_190_, 1);
v___x_195_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0));
v_sz_196_ = lean_array_size(v_val_194_);
v___x_197_ = ((size_t)0ULL);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_171_, v_e_155_, v_val_194_, v_sz_196_, v___x_197_, v___x_195_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_val_194_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_212_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_fst_203_; 
v_fst_203_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_fst_203_);
lean_dec(v_a_199_);
if (lean_obj_tag(v_fst_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3));
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_204_);
v___x_206_ = v___x_201_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
else
{
lean_object* v_val_208_; lean_object* v___x_210_; 
v_val_208_ = lean_ctor_get(v_fst_203_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v_fst_203_, 1);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v_val_208_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_val_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_a_213_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_198_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_198_);
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
lean_object* v___x_221_; lean_object* v___x_223_; 
lean_dec(v_a_190_);
lean_dec_ref(v_e_155_);
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_221_);
v___x_223_ = v___x_192_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_e_155_);
v_a_226_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_189_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_189_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec(v_a_184_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v_e_155_);
lean_dec_ref(v_opName_154_);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_234_);
v___x_236_ = v___x_186_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v___x_170_);
lean_dec_ref(v_e_155_);
lean_dec_ref(v_opName_154_);
v_a_239_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_183_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_183_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_a_179_);
lean_dec(v_rhs_177_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v_e_155_);
lean_dec_ref(v_opName_154_);
v___x_247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_247_);
v___x_249_ = v___x_181_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
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
lean_dec(v_rhs_177_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v_e_155_);
lean_dec_ref(v_opName_154_);
v_a_252_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_178_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_178_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_0interp(lean_interpreter_value* stack)
{
lean_object* v_opName_154_ = stack[0].m_obj;
lean_object* v_e_155_ = stack[1].m_obj;
lean_object* v_a_156_ = stack[2].m_obj;
lean_object* v_a_157_ = stack[3].m_obj;
lean_object* v_a_158_ = stack[4].m_obj;
lean_object* v_a_159_ = stack[5].m_obj;
lean_object* v_a_160_ = stack[6].m_obj;
lean_object* v_a_161_ = stack[7].m_obj;
lean_object* v_a_162_ = stack[8].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v_opName_154_, v_e_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___boxed(lean_object* v_opName_261_, lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v_opName_261_, v_e_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
return v_res_271_;
}
}
lean_object* l_reduceBEq(lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = ((lean_object*)(l_reduceBEq___closed__1));
v___x_287_ = ((lean_object*)(l_reduceBEq___closed__2));
v___x_288_ = lean_unsigned_to_nat(4u);
v___x_289_ = l_Lean_Expr_isAppOfArity(v_e_277_, v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref(v_e_277_);
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v___x_286_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
return v___x_292_;
}
}
}
LEAN_EXPORT void l_reduceBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_277_ = stack[0].m_obj;
lean_object* v_a_278_ = stack[1].m_obj;
lean_object* v_a_279_ = stack[2].m_obj;
lean_object* v_a_280_ = stack[3].m_obj;
lean_object* v_a_281_ = stack[4].m_obj;
lean_object* v_a_282_ = stack[5].m_obj;
lean_object* v_a_283_ = stack[6].m_obj;
lean_object* v_a_284_ = stack[7].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_reduceBEq(v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_reduceBEq___boxed(lean_object* v_e_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_reduceBEq(v_e_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
return v_res_303_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_));
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_));
v___x_322_ = lean_alloc_closure((void*)(l_reduceBEq___boxed), 9, 0);
v___x_323_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_320_, v___x_321_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_324_;
v_res_324_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_();
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20____boxed(lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_();
return v_res_326_;
}
}
lean_object* l_reduceOrd(lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_341_ = ((lean_object*)(l_reduceOrd___closed__1));
v___x_342_ = ((lean_object*)(l_reduceOrd___closed__2));
v___x_343_ = lean_unsigned_to_nat(4u);
v___x_344_ = l_Lean_Expr_isAppOfArity(v_e_332_, v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v_e_332_);
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2));
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(v___x_341_, v_e_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_347_;
}
}
}
LEAN_EXPORT void l_reduceOrd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_332_ = stack[0].m_obj;
lean_object* v_a_333_ = stack[1].m_obj;
lean_object* v_a_334_ = stack[2].m_obj;
lean_object* v_a_335_ = stack[3].m_obj;
lean_object* v_a_336_ = stack[4].m_obj;
lean_object* v_a_337_ = stack[5].m_obj;
lean_object* v_a_338_ = stack[6].m_obj;
lean_object* v_a_339_ = stack[7].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_reduceOrd(v_e_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_reduceOrd___boxed(lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_reduceOrd(v_e_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
return v_res_358_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_));
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_));
v___x_377_ = lean_alloc_closure((void*)(l_reduceOrd___boxed), 9, 0);
v___x_378_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_375_, v___x_376_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_379_;
v_res_379_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_();
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18____boxed(lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_();
return v_res_381_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MethodSpecs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_1805576928____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4136800390____hygCtx___hyg_18_();
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
