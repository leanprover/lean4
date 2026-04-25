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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceGetElem"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(165, 166, 67, 219, 153, 110, 19, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_reduceGetElem___redArg___closed__3_value),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceGetElem\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(29, 44, 253, 173, 103, 75, 126, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__2_value),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Array_reduceGetElem_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "getElem!"};
static const lean_object* l_Array_reduceGetElem_x21___redArg___closed__0 = (const lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__0_value;
static const lean_ctor_object l_Array_reduceGetElem_x21___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_reduceGetElem_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 194, 21, 171, 76, 210, 17)}};
static const lean_ctor_object l_Array_reduceGetElem_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__1_value_aux_0),((lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 107, 135, 132, 224, 239, 185, 227)}};
static const lean_object* l_Array_reduceGetElem_x21___redArg___closed__1 = (const lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceGetElem!"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(88, 59, 74, 68, 2, 195, 24, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_reduceGetElem_x21___redArg___closed__1_value),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_8_, v_a_10_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_95_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_95_ == 0)
{
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_95_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_95_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l_Lean_Expr_cleanupAnnotations(v_a_15_);
v___x_25_ = l_Lean_Expr_isApp(v___x_24_);
if (v___x_25_ == 0)
{
lean_dec_ref(v___x_24_);
goto v___jp_19_;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = l_Lean_Expr_appFnCleanup___redArg(v___x_24_);
v___x_27_ = l_Lean_Expr_isApp(v___x_26_);
if (v___x_27_ == 0)
{
lean_dec_ref(v___x_26_);
goto v___jp_19_;
}
else
{
lean_object* v_arg_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_arg_28_ = lean_ctor_get(v___x_26_, 1);
lean_inc_ref(v_arg_28_);
v___x_29_ = l_Lean_Expr_appFnCleanup___redArg(v___x_26_);
v___x_30_ = l_Lean_Expr_isApp(v___x_29_);
if (v___x_30_ == 0)
{
lean_dec_ref(v___x_29_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v_arg_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_arg_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc_ref(v_arg_31_);
v___x_32_ = l_Lean_Expr_appFnCleanup___redArg(v___x_29_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v___x_32_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
v___x_35_ = l_Lean_Expr_isApp(v___x_34_);
if (v___x_35_ == 0)
{
lean_dec_ref(v___x_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = l_Lean_Expr_appFnCleanup___redArg(v___x_34_);
v___x_37_ = l_Lean_Expr_isApp(v___x_36_);
if (v___x_37_ == 0)
{
lean_dec_ref(v___x_36_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_36_);
v___x_39_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_38_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_41_ = l_Lean_Expr_isApp(v___x_40_);
if (v___x_41_ == 0)
{
lean_dec_ref(v___x_40_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_42_ = l_Lean_Expr_appFnCleanup___redArg(v___x_40_);
v___x_43_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__3));
v___x_44_ = l_Lean_Expr_isConstOf(v___x_42_, v___x_43_);
lean_dec_ref(v___x_42_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_19_;
}
else
{
lean_object* v___x_45_; 
lean_del_object(v___x_17_);
v___x_45_ = l_Lean_Meta_getNatValue_x3f(v_arg_28_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_arg_28_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_86_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_86_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_86_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_86_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
if (lean_obj_tag(v_a_46_) == 1)
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_del_object(v___x_48_);
v_val_50_ = lean_ctor_get(v_a_46_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_a_46_);
v___x_51_ = l_Lean_Meta_getArrayLit_x3f(v_arg_31_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_arg_31_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_73_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_73_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_73_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_73_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
if (lean_obj_tag(v_a_52_) == 1)
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_68_; 
v_val_56_ = lean_ctor_get(v_a_52_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_a_52_);
if (v_isSharedCheck_68_ == 0)
{
v___x_58_ = v_a_52_;
v_isShared_59_ = v_isSharedCheck_68_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_a_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_68_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_60_ = l_Lean_instInhabitedExpr;
v___x_61_ = lean_array_get(v___x_60_, v_val_56_, v_val_50_);
lean_dec(v_val_50_);
lean_dec(v_val_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 0);
lean_ctor_set(v___x_58_, 0, v___x_61_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_67_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_65_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_63_);
v___x_65_ = v___x_54_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_71_; 
lean_dec(v_a_52_);
lean_dec(v_val_50_);
v___x_69_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_69_);
v___x_71_ = v___x_54_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
lean_dec(v_val_50_);
v_a_74_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_51_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_51_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
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
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_a_46_);
lean_dec_ref(v_arg_31_);
v___x_82_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_82_);
v___x_84_ = v___x_48_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec_ref(v_arg_31_);
v_a_87_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_45_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_45_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
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
v___jp_19_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_20_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_14_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_14_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem___redArg___boxed(lean_object* v_e_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Array_reduceGetElem___redArg(v_e_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem(lean_object* v_e_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Array_reduceGetElem___redArg(v_e_111_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem___boxed(lean_object* v_e_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Array_reduceGetElem(v_e_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_));
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_));
v___x_169_ = lean_alloc_closure((void*)(l_Array_reduceGetElem___boxed), 9, 0);
v___x_170_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_167_, v___x_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22____boxed(lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_();
return v_res_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_alloc_closure((void*)(l_Array_reduceGetElem___boxed), 9, 0);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_));
v___x_177_ = 1;
v___x_178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_);
v___x_179_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_176_, v___x_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24____boxed(lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_();
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_));
v___x_184_ = 1;
v___x_185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_);
v___x_186_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_183_, v___x_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26____boxed(lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg(lean_object* v_e_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_r_201_; lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_194_, v_a_196_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_295_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_295_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_295_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_295_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = l_Lean_Expr_cleanupAnnotations(v_a_205_);
v___x_215_ = l_Lean_Expr_isApp(v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___x_214_);
goto v___jp_209_;
}
else
{
lean_object* v_arg_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_arg_216_ = lean_ctor_get(v___x_214_, 1);
lean_inc_ref(v_arg_216_);
v___x_217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_214_);
v___x_218_ = l_Lean_Expr_isApp(v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v___x_217_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v_arg_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_arg_219_ = lean_ctor_get(v___x_217_, 1);
lean_inc_ref(v_arg_219_);
v___x_220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_217_);
v___x_221_ = l_Lean_Expr_isApp(v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v___x_220_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = l_Lean_Expr_appFnCleanup___redArg(v___x_220_);
v___x_223_ = l_Lean_Expr_isApp(v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_222_);
v___x_225_ = l_Lean_Expr_isApp(v___x_224_);
if (v___x_225_ == 0)
{
lean_dec_ref(v___x_224_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v_arg_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_arg_226_ = lean_ctor_get(v___x_224_, 1);
lean_inc_ref(v_arg_226_);
v___x_227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_224_);
v___x_228_ = l_Lean_Expr_isApp(v___x_227_);
if (v___x_228_ == 0)
{
lean_dec_ref(v___x_227_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_227_);
v___x_230_ = l_Lean_Expr_isApp(v___x_229_);
if (v___x_230_ == 0)
{
lean_dec_ref(v___x_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = l_Lean_Expr_appFnCleanup___redArg(v___x_229_);
v___x_232_ = ((lean_object*)(l_Array_reduceGetElem_x3f___redArg___closed__2));
v___x_233_ = l_Lean_Expr_isConstOf(v___x_231_, v___x_232_);
lean_dec_ref(v___x_231_);
if (v___x_233_ == 0)
{
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
goto v___jp_209_;
}
else
{
lean_object* v___x_234_; 
lean_del_object(v___x_207_);
v___x_234_ = l_Lean_Meta_getNatValue_x3f(v_arg_216_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec_ref(v_arg_216_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_286_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_286_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_286_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_286_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
if (lean_obj_tag(v_a_235_) == 1)
{
lean_object* v_val_239_; lean_object* v___x_240_; 
lean_del_object(v___x_237_);
v_val_239_ = lean_ctor_get(v_a_235_, 0);
lean_inc(v_val_239_);
lean_dec_ref(v_a_235_);
v___x_240_ = l_Lean_Meta_getArrayLit_x3f(v_arg_219_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec_ref(v_arg_219_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_273_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_273_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_273_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_273_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
if (lean_obj_tag(v_a_241_) == 1)
{
lean_object* v_val_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
lean_del_object(v___x_243_);
v_val_245_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_val_245_);
lean_dec_ref(v_a_241_);
v___x_246_ = lean_array_get_size(v_val_245_);
v___x_247_ = lean_nat_dec_lt(v_val_239_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_val_245_);
lean_dec(v_val_239_);
v___x_248_ = l_Lean_Meta_mkNone(v_arg_226_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v___x_248_);
v_r_201_ = v_a_249_;
goto v___jp_200_;
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
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_array_fget(v_val_245_, v_val_239_);
lean_dec(v_val_239_);
lean_dec(v_val_245_);
v___x_259_ = l_Lean_Meta_mkSome(v_arg_226_, v___x_258_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref(v___x_259_);
v_r_201_ = v_a_260_;
goto v___jp_200_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_259_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_271_; 
lean_dec(v_a_241_);
lean_dec(v_val_239_);
lean_dec_ref(v_arg_226_);
v___x_269_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_269_);
v___x_271_ = v___x_243_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_val_239_);
lean_dec_ref(v_arg_226_);
v_a_274_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_240_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_240_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec(v_a_235_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_219_);
v___x_282_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_282_);
v___x_284_ = v___x_237_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_219_);
v_a_287_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_234_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_234_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
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
}
}
}
}
}
}
}
v___jp_209_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_212_ = v___x_207_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_a_296_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_204_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_204_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_r_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___redArg___boxed(lean_object* v_e_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Array_reduceGetElem_x3f___redArg(v_e_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Array_reduceGetElem_x3f___redArg(v_e_311_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x3f___boxed(lean_object* v_e_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Array_reduceGetElem_x3f(v_e_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_));
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_));
v___x_356_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x3f___boxed), 9, 0);
v___x_357_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_354_, v___x_355_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21____boxed(lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_();
return v_res_359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x3f___boxed), 9, 0);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_));
v___x_364_ = 1;
v___x_365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_);
v___x_366_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_363_, v___x_364_, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23____boxed(lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_));
v___x_371_ = 1;
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_);
v___x_373_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_370_, v___x_371_, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25____boxed(lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_();
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg(lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_r_387_; lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_380_, v_a_382_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_473_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_473_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_473_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_473_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = l_Lean_Expr_cleanupAnnotations(v_a_391_);
v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v___x_400_);
goto v___jp_395_;
}
else
{
lean_object* v_arg_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_arg_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc_ref(v_arg_402_);
v___x_403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v___x_403_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v_arg_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_arg_405_ = lean_ctor_get(v___x_403_, 1);
lean_inc_ref(v_arg_405_);
v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_407_ = l_Lean_Expr_isApp(v___x_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v___x_406_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_406_);
v___x_409_ = l_Lean_Expr_isApp(v___x_408_);
if (v___x_409_ == 0)
{
lean_dec_ref(v___x_408_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_408_);
v___x_411_ = l_Lean_Expr_isApp(v___x_410_);
if (v___x_411_ == 0)
{
lean_dec_ref(v___x_410_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_410_);
v___x_413_ = l_Lean_Expr_isApp(v___x_412_);
if (v___x_413_ == 0)
{
lean_dec_ref(v___x_412_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v_arg_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_arg_414_ = lean_ctor_get(v___x_412_, 1);
lean_inc_ref(v_arg_414_);
v___x_415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_412_);
v___x_416_ = l_Lean_Expr_isApp(v___x_415_);
if (v___x_416_ == 0)
{
lean_dec_ref(v___x_415_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = l_Lean_Expr_appFnCleanup___redArg(v___x_415_);
v___x_418_ = l_Lean_Expr_isApp(v___x_417_);
if (v___x_418_ == 0)
{
lean_dec_ref(v___x_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_419_ = l_Lean_Expr_appFnCleanup___redArg(v___x_417_);
v___x_420_ = ((lean_object*)(l_Array_reduceGetElem_x21___redArg___closed__1));
v___x_421_ = l_Lean_Expr_isConstOf(v___x_419_, v___x_420_);
lean_dec_ref(v___x_419_);
if (v___x_421_ == 0)
{
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_395_;
}
else
{
lean_object* v___x_422_; 
lean_del_object(v___x_393_);
v___x_422_ = l_Lean_Meta_getNatValue_x3f(v_arg_402_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec_ref(v_arg_402_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_464_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_464_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_464_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_464_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
if (lean_obj_tag(v_a_423_) == 1)
{
lean_object* v_val_427_; lean_object* v___x_428_; 
lean_del_object(v___x_425_);
v_val_427_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_val_427_);
lean_dec_ref(v_a_423_);
v___x_428_ = l_Lean_Meta_getArrayLit_x3f(v_arg_405_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec_ref(v_arg_405_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_451_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_451_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_451_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_451_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
if (lean_obj_tag(v_a_429_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
lean_del_object(v___x_431_);
v_val_433_ = lean_ctor_get(v_a_429_, 0);
lean_inc(v_val_433_);
lean_dec_ref(v_a_429_);
v___x_434_ = lean_array_get_size(v_val_433_);
v___x_435_ = lean_nat_dec_lt(v_val_427_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_dec(v_val_433_);
lean_dec(v_val_427_);
v___x_436_ = l_Lean_Meta_mkDefault(v_arg_414_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
v_r_387_ = v_a_437_;
goto v___jp_386_;
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_436_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v___x_446_; 
lean_dec_ref(v_arg_414_);
v___x_446_ = lean_array_fget(v_val_433_, v_val_427_);
lean_dec(v_val_427_);
lean_dec(v_val_433_);
v_r_387_ = v___x_446_;
goto v___jp_386_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_dec(v_a_429_);
lean_dec(v_val_427_);
lean_dec_ref(v_arg_414_);
v___x_447_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_447_);
v___x_449_ = v___x_431_;
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
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_val_427_);
lean_dec_ref(v_arg_414_);
v_a_452_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_428_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_428_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_a_423_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_405_);
v___x_460_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_460_);
v___x_462_ = v___x_425_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
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
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_405_);
v_a_465_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_422_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_422_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
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
v___jp_395_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = ((lean_object*)(l_Array_reduceGetElem___redArg___closed__0));
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_a_474_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_390_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_390_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_r_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___redArg___boxed(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Array_reduceGetElem_x21___redArg(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21(lean_object* v_e_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Array_reduceGetElem_x21___redArg(v_e_489_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceGetElem_x21___boxed(lean_object* v_e_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Array_reduceGetElem_x21(v_e_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_));
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_));
v___x_535_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x21___boxed), 9, 0);
v___x_536_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_533_, v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21____boxed(lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_();
return v_res_538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_alloc_closure((void*)(l_Array_reduceGetElem_x21___boxed), 9, 0);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_));
v___x_543_ = 1;
v___x_544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_);
v___x_545_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_542_, v___x_543_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23____boxed(lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_();
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_));
v___x_550_ = 1;
v___x_551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_);
v___x_552_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_549_, v___x_550_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25____boxed(lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_();
return v_res_554_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_();
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
