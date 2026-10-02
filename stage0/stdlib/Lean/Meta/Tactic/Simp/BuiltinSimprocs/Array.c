// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Array
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
static const lean_ctor_object l_Array_reduceGetElem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_reduceGetElem___redArg___closed__0 = (const lean_object*)&l_Array_reduceGetElem___redArg___closed__0_value;
static const lean_string_object l_Array_reduceGetElem___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l_Array_reduceGetElem___redArg___closed__1 = (const lean_object*)&l_Array_reduceGetElem___redArg___closed__1_value;
static const lean_string_object l_Array_reduceGetElem___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l_Array_reduceGetElem___redArg___closed__2 = (const lean_object*)&l_Array_reduceGetElem___redArg___closed__2_value;
static const lean_ctor_object l_Array_reduceGetElem___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_reduceGetElem___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 233, 51, 226, 114, 128, 218, 11)}};
static const lean_ctor_object l_Array_reduceGetElem___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_reduceGetElem___redArg___closed__3_value_aux_0),((lean_object*)&l_Array_reduceGetElem___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 164, 165, 74, 8, 252, 37, 122)}};
static const lean_object* l_Array_reduceGetElem___redArg___closed__3 = (const lean_object*)&l_Array_reduceGetElem___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceGetElem"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(165, 166, 67, 219, 153, 110, 19, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_reduceGetElem___redArg___closed__3_value),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33____boxed(lean_object*);
static const lean_string_object l_Array_reduceGetElem_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "GetElem\?"};
static const lean_object* l_Array_reduceGetElem_x3f___redArg___closed__0 = (const lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__0_value;
static const lean_string_object l_Array_reduceGetElem_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "getElem\?"};
static const lean_object* l_Array_reduceGetElem_x3f___redArg___closed__1 = (const lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Array_reduceGetElem_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 194, 21, 171, 76, 210, 17)}};
static const lean_ctor_object l_Array_reduceGetElem_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 183, 124, 210, 168, 65, 205)}};
static const lean_object* l_Array_reduceGetElem_x3f___redArg___closed__2 = (const lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceGetElem\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(29, 44, 253, 173, 103, 75, 126, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__2_value),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32____boxed(lean_object*);
static const lean_string_object l_Array_reduceGetElem_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "getElem!"};
static const lean_object* l_Array_reduceGetElem_x21___redArg___closed__0 = (const lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__0_value;
static const lean_ctor_object l_Array_reduceGetElem_x21___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 194, 21, 171, 76, 210, 17)}};
static const lean_ctor_object l_Array_reduceGetElem_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__1_value_aux_0),((lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 107, 135, 132, 224, 239, 185, 227)}};
static const lean_object* l_Array_reduceGetElem_x21___redArg___closed__1 = (const lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceGetElem!"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value),LEAN_SCALAR_PTR_LITERAL(88, 59, 74, 68, 2, 195, 24, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__1_value),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Lean_instInhabitedExpr;
v___x_18_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_8_, v_a_10_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_20_ = l_Lean_Expr_cleanupAnnotations(v_a_19_);
v___x_21_ = l_Lean_Expr_isApp(v___x_20_);
if (v___x_21_ == 0)
{
lean_dec_ref(v___x_20_);
goto v___jp_14_;
}
else
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = l_Lean_Expr_appFnCleanup___redArg(v___x_20_);
v___x_23_ = l_Lean_Expr_isApp(v___x_22_);
if (v___x_23_ == 0)
{
lean_dec_ref(v___x_22_);
goto v___jp_14_;
}
else
{
lean_object* v_arg_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_arg_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc_ref(v_arg_24_);
v___x_25_ = l_Lean_Expr_appFnCleanup___redArg(v___x_22_);
v___x_26_ = l_Lean_Expr_isApp(v___x_25_);
if (v___x_26_ == 0)
{
lean_dec_ref(v___x_25_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v_arg_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_arg_27_ = lean_ctor_get(v___x_25_, 1);
lean_inc_ref(v_arg_27_);
v___x_28_ = l_Lean_Expr_appFnCleanup___redArg(v___x_25_);
v___x_29_ = l_Lean_Expr_isApp(v___x_28_);
if (v___x_29_ == 0)
{
lean_dec_ref(v___x_28_);
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = l_Lean_Expr_appFnCleanup___redArg(v___x_28_);
v___x_31_ = l_Lean_Expr_isApp(v___x_30_);
if (v___x_31_ == 0)
{
lean_dec_ref(v___x_30_);
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = l_Lean_Expr_appFnCleanup___redArg(v___x_30_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v___x_32_);
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
v___x_35_ = l_Lean_Expr_isApp(v___x_34_);
if (v___x_35_ == 0)
{
lean_dec_ref(v___x_34_);
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = l_Lean_Expr_appFnCleanup___redArg(v___x_34_);
v___x_37_ = l_Lean_Expr_isApp(v___x_36_);
if (v___x_37_ == 0)
{
lean_dec_ref(v___x_36_);
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_36_);
v___x_39_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__3));
v___x_40_ = l_Lean_Expr_isConstOf(v___x_38_, v___x_39_);
lean_dec_ref(v___x_38_);
if (v___x_40_ == 0)
{
lean_dec_ref(v_arg_27_);
lean_dec_ref(v_arg_24_);
goto v___jp_14_;
}
else
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_getNatValue_x3f(v_arg_24_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_arg_24_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_81_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_81_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_81_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_81_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
if (lean_obj_tag(v_a_42_) == 1)
{
lean_object* v_val_46_; lean_object* v___x_47_; 
lean_del_object(v___x_44_);
v_val_46_ = lean_ctor_get(v_a_42_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_a_42_, 1);
v___x_47_ = l_Lean_Meta_getArrayLit_x3f(v_arg_27_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_arg_27_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_68_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_68_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_68_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_68_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
if (lean_obj_tag(v_a_48_) == 1)
{
lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_63_; 
v_val_52_ = lean_ctor_get(v_a_48_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_a_48_);
if (v_isSharedCheck_63_ == 0)
{
v___x_54_ = v_a_48_;
v_isShared_55_ = v_isSharedCheck_63_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v_a_48_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_63_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = lean_array_get(v___x_17_, v_val_52_, v_val_46_);
lean_dec(v_val_46_);
lean_dec(v_val_52_);
if (v_isShared_55_ == 0)
{
lean_ctor_set_tag(v___x_54_, 0);
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_58_ = v___x_54_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_62_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_60_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_58_);
v___x_60_ = v___x_50_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
else
{
lean_object* v___x_64_; lean_object* v___x_66_; 
lean_dec(v_a_48_);
lean_dec(v_val_46_);
v___x_64_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_64_);
v___x_66_ = v___x_50_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
lean_dec(v_val_46_);
v_a_69_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_47_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_47_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
else
{
lean_object* v___x_77_; lean_object* v___x_79_; 
lean_dec(v_a_42_);
lean_dec_ref(v_arg_27_);
v___x_77_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_77_);
v___x_79_ = v___x_44_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec_ref(v_arg_27_);
v_a_82_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_41_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_41_);
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
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_a_90_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_18_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_18_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
v___jp_14_:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg___boxed(lean_object* v_e_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Array_reduceGetElem___redArg(v_e_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem(lean_object* v_e_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Array_reduceGetElem___redArg(v_e_105_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem___boxed(lean_object* v_e_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Array_reduceGetElem(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_163_ = lean_alloc_closure((void*)(l_Array_reduceGetElem___boxed), 9, 0);
v___x_164_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_161_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29____boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_();
return v_res_166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_alloc_closure((void*)(l_Array_reduceGetElem___boxed), 9, 0);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_171_ = 1;
v___x_172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_);
v___x_173_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_170_, v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31____boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_(){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_178_ = 1;
v___x_179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_);
v___x_180_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_177_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33____boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg(lean_object* v_e_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_r_198_; lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_188_, v_a_190_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = l_Lean_Expr_cleanupAnnotations(v_a_202_);
v___x_204_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_204_ == 0)
{
lean_dec_ref(v___x_203_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_arg_205_ = lean_ctor_get(v___x_203_, 1);
lean_inc_ref(v_arg_205_);
v___x_206_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
v___x_207_ = l_Lean_Expr_isApp(v___x_206_);
if (v___x_207_ == 0)
{
lean_dec_ref(v___x_206_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_arg_208_ = lean_ctor_get(v___x_206_, 1);
lean_inc_ref(v_arg_208_);
v___x_209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_206_);
v___x_210_ = l_Lean_Expr_isApp(v___x_209_);
if (v___x_210_ == 0)
{
lean_dec_ref(v___x_209_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_212_ = l_Lean_Expr_isApp(v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v___x_211_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_211_);
v___x_214_ = l_Lean_Expr_isApp(v___x_213_);
if (v___x_214_ == 0)
{
lean_dec_ref(v___x_213_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_arg_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc_ref(v_arg_215_);
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_213_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_219_ = l_Lean_Expr_isApp(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v___x_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_218_);
v___x_221_ = ((lean_object*)(l_Array_reduceGetElem_x3f___redArg___closed__2));
v___x_222_ = l_Lean_Expr_isConstOf(v___x_220_, v___x_221_);
lean_dec_ref(v___x_220_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_194_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Meta_getNatValue_x3f(v_arg_205_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec_ref(v_arg_205_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_275_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_275_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_275_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_275_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
if (lean_obj_tag(v_a_224_) == 1)
{
lean_object* v_val_228_; lean_object* v___x_229_; 
lean_del_object(v___x_226_);
v_val_228_ = lean_ctor_get(v_a_224_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v_a_224_, 1);
v___x_229_ = l_Lean_Meta_getArrayLit_x3f(v_arg_208_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec_ref(v_arg_208_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_262_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_262_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_262_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_262_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
if (lean_obj_tag(v_a_230_) == 1)
{
lean_object* v_val_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
lean_del_object(v___x_232_);
v_val_234_ = lean_ctor_get(v_a_230_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v_a_230_, 1);
v___x_235_ = lean_array_get_size(v_val_234_);
v___x_236_ = lean_nat_dec_lt(v_val_228_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_val_234_);
lean_dec(v_val_228_);
v___x_237_ = l_Lean_Meta_mkNone(v_arg_215_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v_r_198_ = v_a_238_;
goto v___jp_197_;
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_237_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_237_);
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
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_array_fget(v_val_234_, v_val_228_);
lean_dec(v_val_228_);
lean_dec(v_val_234_);
v___x_248_ = l_Lean_Meta_mkSome(v_arg_215_, v___x_247_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v_r_198_ = v_a_249_;
goto v___jp_197_;
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_248_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_248_);
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
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v_a_230_);
lean_dec(v_val_228_);
lean_dec_ref(v_arg_215_);
v___x_258_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_258_);
v___x_260_ = v___x_232_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_val_228_);
lean_dec_ref(v_arg_215_);
v_a_263_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_229_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_229_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_a_224_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_208_);
v___x_271_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_271_);
v___x_273_ = v___x_226_;
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
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_208_);
v_a_276_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_223_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_223_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
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
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_201_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_201_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
v___jp_194_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v_r_198_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg___boxed(lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Array_reduceGetElem_x3f___redArg(v_e_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f(lean_object* v_e_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Array_reduceGetElem_x3f___redArg(v_e_299_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___boxed(lean_object* v_e_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Array_reduceGetElem_x3f(v_e_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_344_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x3f___boxed), 9, 0);
v___x_345_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_342_, v___x_343_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28____boxed(lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_();
return v_res_347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x3f___boxed), 9, 0);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_352_ = 1;
v___x_353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_);
v___x_354_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_351_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_();
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_359_ = 1;
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_);
v___x_361_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_358_, v___x_359_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32____boxed(lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_();
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg(lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_r_378_; lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_368_, v_a_370_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
v___x_383_ = l_Lean_Expr_cleanupAnnotations(v_a_382_);
v___x_384_ = l_Lean_Expr_isApp(v___x_383_);
if (v___x_384_ == 0)
{
lean_dec_ref(v___x_383_);
goto v___jp_374_;
}
else
{
lean_object* v_arg_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_arg_385_ = lean_ctor_get(v___x_383_, 1);
lean_inc_ref(v_arg_385_);
v___x_386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_383_);
v___x_387_ = l_Lean_Expr_isApp(v___x_386_);
if (v___x_387_ == 0)
{
lean_dec_ref(v___x_386_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v_arg_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_arg_388_ = lean_ctor_get(v___x_386_, 1);
lean_inc_ref(v_arg_388_);
v___x_389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_386_);
v___x_390_ = l_Lean_Expr_isApp(v___x_389_);
if (v___x_390_ == 0)
{
lean_dec_ref(v___x_389_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_389_);
v___x_392_ = l_Lean_Expr_isApp(v___x_391_);
if (v___x_392_ == 0)
{
lean_dec_ref(v___x_391_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_391_);
v___x_394_ = l_Lean_Expr_isApp(v___x_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v___x_393_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_393_);
v___x_396_ = l_Lean_Expr_isApp(v___x_395_);
if (v___x_396_ == 0)
{
lean_dec_ref(v___x_395_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v_arg_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_arg_397_ = lean_ctor_get(v___x_395_, 1);
lean_inc_ref(v_arg_397_);
v___x_398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_395_);
v___x_399_ = l_Lean_Expr_isApp(v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v___x_398_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_398_);
v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v___x_400_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
v___x_403_ = ((lean_object*)(l_Array_reduceGetElem_x21___redArg___closed__1));
v___x_404_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_403_);
lean_dec_ref(v___x_402_);
if (v___x_404_ == 0)
{
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_388_);
lean_dec_ref(v_arg_385_);
goto v___jp_374_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_getNatValue_x3f(v_arg_385_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec_ref(v_arg_385_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_447_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_447_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_447_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_447_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
if (lean_obj_tag(v_a_406_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_411_; 
lean_del_object(v___x_408_);
v_val_410_ = lean_ctor_get(v_a_406_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_a_406_, 1);
v___x_411_ = l_Lean_Meta_getArrayLit_x3f(v_arg_388_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec_ref(v_arg_388_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_434_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_434_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_434_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_434_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
if (lean_obj_tag(v_a_412_) == 1)
{
lean_object* v_val_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
lean_del_object(v___x_414_);
v_val_416_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_val_416_);
lean_dec_ref_known(v_a_412_, 1);
v___x_417_ = lean_array_get_size(v_val_416_);
v___x_418_ = lean_nat_dec_lt(v_val_410_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v_val_416_);
lean_dec(v_val_410_);
v___x_419_ = l_Lean_Meta_mkDefault(v_arg_397_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v_r_378_ = v_a_420_;
goto v___jp_377_;
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_419_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v___x_429_; 
lean_dec_ref(v_arg_397_);
v___x_429_ = lean_array_fget(v_val_416_, v_val_410_);
lean_dec(v_val_410_);
lean_dec(v_val_416_);
v_r_378_ = v___x_429_;
goto v___jp_377_;
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec(v_a_412_);
lean_dec(v_val_410_);
lean_dec_ref(v_arg_397_);
v___x_430_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_430_);
v___x_432_ = v___x_414_;
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
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_val_410_);
lean_dec_ref(v_arg_397_);
v_a_435_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_411_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_411_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec(v_a_406_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_388_);
v___x_443_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_443_);
v___x_445_ = v___x_408_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
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
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_388_);
v_a_448_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_405_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_405_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
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
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_381_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_381_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
v___jp_374_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
v___jp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_r_378_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Array_reduceGetElem_x21___redArg(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Array_reduceGetElem_x21___redArg(v_e_471_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___boxed(lean_object* v_e_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Array_reduceGetElem_x21(v_e_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_517_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x21___boxed), 9, 0);
v___x_518_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_515_, v___x_516_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28____boxed(lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_();
return v_res_520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x21___boxed), 9, 0);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_525_ = 1;
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_);
v___x_527_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_524_, v___x_525_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30____boxed(lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_();
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_532_ = 1;
v___x_533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_);
v___x_534_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_531_, v___x_532_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32____boxed(lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_();
return v_res_536_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
}
#ifdef __cplusplus
}
#endif
