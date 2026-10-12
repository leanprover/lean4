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
lean_object* l_Array_reduceGetElem___redArg(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l_Array_reduceGetElem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_8_ = stack[0].m_obj;
lean_object* v_a_9_ = stack[1].m_obj;
lean_object* v_a_10_ = stack[2].m_obj;
lean_object* v_a_11_ = stack[3].m_obj;
lean_object* v_a_12_ = stack[4].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Array_reduceGetElem___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg___boxed(lean_object* v_e_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Array_reduceGetElem___redArg(v_e_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
return v_res_105_;
}
}
lean_object* l_Array_reduceGetElem(lean_object* v_e_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Array_reduceGetElem___redArg(v_e_106_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_115_;
}
}
LEAN_EXPORT void l_Array_reduceGetElem_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_106_ = stack[0].m_obj;
lean_object* v_a_107_ = stack[1].m_obj;
lean_object* v_a_108_ = stack[2].m_obj;
lean_object* v_a_109_ = stack[3].m_obj;
lean_object* v_a_110_ = stack[4].m_obj;
lean_object* v_a_111_ = stack[5].m_obj;
lean_object* v_a_112_ = stack[6].m_obj;
lean_object* v_a_113_ = stack[7].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Array_reduceGetElem(v_e_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem___boxed(lean_object* v_e_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Array_reduceGetElem(v_e_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_126_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_165_ = lean_alloc_closure((void*)(l_Array_reduceGetElem___boxed), 9, 0);
v___x_166_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_163_, v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_167_;
v_res_167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_();
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29____boxed(lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_();
return v_res_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_alloc_closure((void*)(l_Array_reduceGetElem___boxed), 9, 0);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_174_ = 1;
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_);
v___x_176_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_173_, v___x_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_177_;
v_res_177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_();
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31____boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_();
return v_res_179_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_(){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_29_));
v___x_182_ = 1;
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_31_);
v___x_184_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_181_, v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_185_;
v_res_185_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_();
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33____boxed(lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_697310858____hygCtx___hyg_33_();
return v_res_187_;
}
}
lean_object* l_Array_reduceGetElem_x3f___redArg(lean_object* v_e_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_r_203_; lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_193_, v_a_195_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = l_Lean_Expr_cleanupAnnotations(v_a_207_);
v___x_209_ = l_Lean_Expr_isApp(v___x_208_);
if (v___x_209_ == 0)
{
lean_dec_ref(v___x_208_);
goto v___jp_199_;
}
else
{
lean_object* v_arg_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_arg_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc_ref(v_arg_210_);
v___x_211_ = l_Lean_Expr_appFnCleanup___redArg(v___x_208_);
v___x_212_ = l_Lean_Expr_isApp(v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v___x_211_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v_arg_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_arg_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc_ref(v_arg_213_);
v___x_214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_211_);
v___x_215_ = l_Lean_Expr_isApp(v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___x_214_);
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_214_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_219_ = l_Lean_Expr_isApp(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v___x_218_);
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v_arg_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_arg_220_ = lean_ctor_get(v___x_218_, 1);
lean_inc_ref(v_arg_220_);
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_218_);
v___x_222_ = l_Lean_Expr_isApp(v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v___x_221_);
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_221_);
v___x_224_ = l_Lean_Expr_isApp(v___x_223_);
if (v___x_224_ == 0)
{
lean_dec_ref(v___x_223_);
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_223_);
v___x_226_ = ((lean_object*)(l_Array_reduceGetElem_x3f___redArg___closed__2));
v___x_227_ = l_Lean_Expr_isConstOf(v___x_225_, v___x_226_);
lean_dec_ref(v___x_225_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_210_);
goto v___jp_199_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_getNatValue_x3f(v_arg_210_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec_ref(v_arg_210_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_280_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_280_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_280_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_280_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
if (lean_obj_tag(v_a_229_) == 1)
{
lean_object* v_val_233_; lean_object* v___x_234_; 
lean_del_object(v___x_231_);
v_val_233_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v_a_229_, 1);
v___x_234_ = l_Lean_Meta_getArrayLit_x3f(v_arg_213_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec_ref(v_arg_213_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_267_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_267_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_267_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_267_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
if (lean_obj_tag(v_a_235_) == 1)
{
lean_object* v_val_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
lean_del_object(v___x_237_);
v_val_239_ = lean_ctor_get(v_a_235_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v_a_235_, 1);
v___x_240_ = lean_array_get_size(v_val_239_);
v___x_241_ = lean_nat_dec_lt(v_val_233_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_dec(v_val_239_);
lean_dec(v_val_233_);
v___x_242_ = l_Lean_Meta_mkNone(v_arg_220_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v_r_203_ = v_a_243_;
goto v___jp_202_;
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_242_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_242_);
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
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_array_fget(v_val_239_, v_val_233_);
lean_dec(v_val_233_);
lean_dec(v_val_239_);
v___x_253_ = l_Lean_Meta_mkSome(v_arg_220_, v___x_252_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v_r_203_ = v_a_254_;
goto v___jp_202_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_253_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
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
}
else
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_dec(v_a_235_);
lean_dec(v_val_233_);
lean_dec_ref(v_arg_220_);
v___x_263_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_263_);
v___x_265_ = v___x_237_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec(v_val_233_);
lean_dec_ref(v_arg_220_);
v_a_268_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_234_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_234_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
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
lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec(v_a_229_);
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_213_);
v___x_276_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_276_);
v___x_278_ = v___x_231_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
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
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_213_);
v_a_281_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_228_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_228_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_206_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_206_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
v___jp_199_:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_r_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT void l_Array_reduceGetElem_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_193_ = stack[0].m_obj;
lean_object* v_a_194_ = stack[1].m_obj;
lean_object* v_a_195_ = stack[2].m_obj;
lean_object* v_a_196_ = stack[3].m_obj;
lean_object* v_a_197_ = stack[4].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Array_reduceGetElem_x3f___redArg(v_e_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg___boxed(lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Array_reduceGetElem_x3f___redArg(v_e_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_304_;
}
}
lean_object* l_Array_reduceGetElem_x3f(lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Array_reduceGetElem_x3f___redArg(v_e_305_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
return v___x_314_;
}
}
LEAN_EXPORT void l_Array_reduceGetElem_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_305_ = stack[0].m_obj;
lean_object* v_a_306_ = stack[1].m_obj;
lean_object* v_a_307_ = stack[2].m_obj;
lean_object* v_a_308_ = stack[3].m_obj;
lean_object* v_a_309_ = stack[4].m_obj;
lean_object* v_a_310_ = stack[5].m_obj;
lean_object* v_a_311_ = stack[6].m_obj;
lean_object* v_a_312_ = stack[7].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Array_reduceGetElem_x3f(v_e_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___boxed(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Array_reduceGetElem_x3f(v_e_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
return v_res_325_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_351_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x3f___boxed), 9, 0);
v___x_352_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_349_, v___x_350_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_353_;
v_res_353_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_();
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28____boxed(lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_();
return v_res_355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x3f___boxed), 9, 0);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_360_ = 1;
v___x_361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_);
v___x_362_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_359_, v___x_360_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_363_;
v_res_363_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_();
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30____boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_();
return v_res_365_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_28_));
v___x_368_ = 1;
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_30_);
v___x_370_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_367_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_371_;
v_res_371_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_();
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32____boxed(lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_4057847622____hygCtx___hyg_32_();
return v_res_373_;
}
}
lean_object* l_Array_reduceGetElem_x21___redArg(lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_r_388_; lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_378_, v_a_380_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = l_Lean_Expr_cleanupAnnotations(v_a_392_);
v___x_394_ = l_Lean_Expr_isApp(v___x_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v___x_393_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_arg_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc_ref(v_arg_395_);
v___x_396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_393_);
v___x_397_ = l_Lean_Expr_isApp(v___x_396_);
if (v___x_397_ == 0)
{
lean_dec_ref(v___x_396_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_arg_398_ = lean_ctor_get(v___x_396_, 1);
lean_inc_ref(v_arg_398_);
v___x_399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_396_);
v___x_400_ = l_Lean_Expr_isApp(v___x_399_);
if (v___x_400_ == 0)
{
lean_dec_ref(v___x_399_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_399_);
v___x_402_ = l_Lean_Expr_isApp(v___x_401_);
if (v___x_402_ == 0)
{
lean_dec_ref(v___x_401_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_401_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v___x_403_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_406_ = l_Lean_Expr_isApp(v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref(v___x_405_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_arg_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc_ref(v_arg_407_);
v___x_408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_405_);
v___x_409_ = l_Lean_Expr_isApp(v___x_408_);
if (v___x_409_ == 0)
{
lean_dec_ref(v___x_408_);
lean_dec_ref(v_arg_407_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_408_);
v___x_411_ = l_Lean_Expr_isApp(v___x_410_);
if (v___x_411_ == 0)
{
lean_dec_ref(v___x_410_);
lean_dec_ref(v_arg_407_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_410_);
v___x_413_ = ((lean_object*)(l_Array_reduceGetElem_x21___redArg___closed__1));
v___x_414_ = l_Lean_Expr_isConstOf(v___x_412_, v___x_413_);
lean_dec_ref(v___x_412_);
if (v___x_414_ == 0)
{
lean_dec_ref(v_arg_407_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
goto v___jp_384_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_getNatValue_x3f(v_arg_395_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_arg_395_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_457_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_457_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_457_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_457_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
if (lean_obj_tag(v_a_416_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_421_; 
lean_del_object(v___x_418_);
v_val_420_ = lean_ctor_get(v_a_416_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_a_416_, 1);
v___x_421_ = l_Lean_Meta_getArrayLit_x3f(v_arg_398_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_arg_398_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_444_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_444_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_444_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_444_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
if (lean_obj_tag(v_a_422_) == 1)
{
lean_object* v_val_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
lean_del_object(v___x_424_);
v_val_426_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_a_422_, 1);
v___x_427_ = lean_array_get_size(v_val_426_);
v___x_428_ = lean_nat_dec_lt(v_val_420_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v_val_426_);
lean_dec(v_val_420_);
v___x_429_ = l_Lean_Meta_mkDefault(v_arg_407_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v_r_388_ = v_a_430_;
goto v___jp_387_;
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v___x_439_; 
lean_dec_ref(v_arg_407_);
v___x_439_ = lean_array_fget(v_val_426_, v_val_420_);
lean_dec(v_val_420_);
lean_dec(v_val_426_);
v_r_388_ = v___x_439_;
goto v___jp_387_;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec(v_a_422_);
lean_dec(v_val_420_);
lean_dec_ref(v_arg_407_);
v___x_440_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_440_);
v___x_442_ = v___x_424_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_val_420_);
lean_dec_ref(v_arg_407_);
v_a_445_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_421_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_421_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec(v_a_416_);
lean_dec_ref(v_arg_407_);
lean_dec_ref(v_arg_398_);
v___x_453_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_453_);
v___x_455_ = v___x_418_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v_arg_407_);
lean_dec_ref(v_arg_398_);
v_a_458_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_415_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_415_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
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
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_a_466_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_391_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_391_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
v___jp_384_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_r_388_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
LEAN_EXPORT void l_Array_reduceGetElem_x21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_378_ = stack[0].m_obj;
lean_object* v_a_379_ = stack[1].m_obj;
lean_object* v_a_380_ = stack[2].m_obj;
lean_object* v_a_381_ = stack[3].m_obj;
lean_object* v_a_382_ = stack[4].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Array_reduceGetElem_x21___redArg(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg___boxed(lean_object* v_e_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Array_reduceGetElem_x21___redArg(v_e_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_481_;
}
}
lean_object* l_Array_reduceGetElem_x21(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Array_reduceGetElem_x21___redArg(v_e_482_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
return v___x_491_;
}
}
LEAN_EXPORT void l_Array_reduceGetElem_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_482_ = stack[0].m_obj;
lean_object* v_a_483_ = stack[1].m_obj;
lean_object* v_a_484_ = stack[2].m_obj;
lean_object* v_a_485_ = stack[3].m_obj;
lean_object* v_a_486_ = stack[4].m_obj;
lean_object* v_a_487_ = stack[5].m_obj;
lean_object* v_a_488_ = stack[6].m_obj;
lean_object* v_a_489_ = stack[7].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Array_reduceGetElem_x21(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___boxed(lean_object* v_e_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Array_reduceGetElem_x21(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
return v_res_502_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_529_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x21___boxed), 9, 0);
v___x_530_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_527_, v___x_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_531_;
v_res_531_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_();
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28____boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_();
return v_res_533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x21___boxed), 9, 0);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_538_ = 1;
v___x_539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_);
v___x_540_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_537_, v___x_538_, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_541_;
v_res_541_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_();
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30____boxed(lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_();
return v_res_543_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_28_));
v___x_546_ = 1;
v___x_547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_30_);
v___x_548_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_545_, v___x_546_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_549_;
v_res_549_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_();
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32____boxed(lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_2146221617____hygCtx___hyg_32_();
return v_res_551_;
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
