// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.String
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
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
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
uint8_t l_String_decLE(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_reduceAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HAppend"};
static const lean_object* l_String_reduceAppend___redArg___closed__0 = (const lean_object*)&l_String_reduceAppend___redArg___closed__0_value;
static const lean_string_object l_String_reduceAppend___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hAppend"};
static const lean_object* l_String_reduceAppend___redArg___closed__1 = (const lean_object*)&l_String_reduceAppend___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceAppend___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceAppend___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 35, 233, 160, 196, 216, 250, 31)}};
static const lean_ctor_object l_String_reduceAppend___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceAppend___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceAppend___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 97, 51, 176, 35, 131, 5, 233)}};
static const lean_object* l_String_reduceAppend___redArg___closed__2 = (const lean_object*)&l_String_reduceAppend___redArg___closed__2_value;
static const lean_ctor_object l_String_reduceAppend___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_reduceAppend___redArg___closed__3 = (const lean_object*)&l_String_reduceAppend___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceAppend"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(130, 179, 20, 139, 17, 100, 1, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceAppend___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_reduceOfList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l_String_reduceOfList___redArg___closed__0 = (const lean_object*)&l_String_reduceOfList___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceOfList___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_reduceOfList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceOfList___redArg___closed__1_value_aux_0),((lean_object*)&l_String_reduceOfList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l_String_reduceOfList___redArg___closed__1 = (const lean_object*)&l_String_reduceOfList___redArg___closed__1_value;
static const lean_string_object l_String_reduceOfList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_reduceOfList___redArg___closed__2 = (const lean_object*)&l_String_reduceOfList___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_String_reduceOfList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceOfList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceOfList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceOfList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceOfList"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(84, 149, 88, 166, 156, 126, 205, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceOfList___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_reduceToList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toList"};
static const lean_object* l_String_reduceToList___redArg___closed__0 = (const lean_object*)&l_String_reduceToList___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceToList___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_reduceToList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceToList___redArg___closed__1_value_aux_0),((lean_object*)&l_String_reduceToList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 127, 118, 127, 34, 206, 216, 161)}};
static const lean_object* l_String_reduceToList___redArg___closed__1 = (const lean_object*)&l_String_reduceToList___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceToList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l_String_reduceToList___redArg___closed__2 = (const lean_object*)&l_String_reduceToList___redArg___closed__2_value;
static lean_once_cell_t l_String_reduceToList___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToList___redArg___closed__3;
static const lean_ctor_object l_String_reduceToList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_reduceToList___redArg___closed__4 = (const lean_object*)&l_String_reduceToList___redArg___closed__4_value;
static lean_once_cell_t l_String_reduceToList___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToList___redArg___closed__5;
static lean_once_cell_t l_String_reduceToList___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToList___redArg___closed__6;
static lean_once_cell_t l_String_reduceToList___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToList___redArg___closed__7;
static lean_once_cell_t l_String_reduceToList___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToList___redArg___closed__8;
LEAN_EXPORT lean_object* l_String_reduceToList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceToList"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(44, 217, 161, 102, 102, 251, 25, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceToList___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_String_reducePush___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "push"};
static const lean_object* l_String_reducePush___redArg___closed__0 = (const lean_object*)&l_String_reducePush___redArg___closed__0_value;
static const lean_ctor_object l_String_reducePush___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_reducePush___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reducePush___redArg___closed__1_value_aux_0),((lean_object*)&l_String_reducePush___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 214, 172, 180, 192, 17, 133, 66)}};
static const lean_object* l_String_reducePush___redArg___closed__1 = (const lean_object*)&l_String_reducePush___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_reducePush___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reducePush___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reducePush(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reducePush___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reducePush"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(73, 35, 175, 29, 202, 201, 229, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reducePush___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_String_reduceSingleton___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "singleton"};
static const lean_object* l_String_reduceSingleton___redArg___closed__0 = (const lean_object*)&l_String_reduceSingleton___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceSingleton___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_reduceSingleton___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceSingleton___redArg___closed__1_value_aux_0),((lean_object*)&l_String_reduceSingleton___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 249, 164, 191, 79, 71, 244, 218)}};
static const lean_object* l_String_reduceSingleton___redArg___closed__1 = (const lean_object*)&l_String_reduceSingleton___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceSingleton___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceSingleton___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceSingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceSingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceSingleton"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(1, 89, 111, 129, 120, 146, 0, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceSingleton___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17____boxed(lean_object*);
static const lean_ctor_object l_String_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_reduceBinPred___redArg___closed__0 = (const lean_object*)&l_String_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_String_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l_String_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l_String_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_String_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l_String_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_String_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_String_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l_String_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l_String_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceBoolPred___redArg___closed__3;
static const lean_string_object l_String_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_String_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l_String_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l_String_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_String_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l_String_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_String_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l_String_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l_String_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_String_reduceLT___redArg___closed__0 = (const lean_object*)&l_String_reduceLT___redArg___closed__0_value;
static const lean_string_object l_String_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_String_reduceLT___redArg___closed__1 = (const lean_object*)&l_String_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_String_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_String_reduceLT___redArg___closed__2 = (const lean_object*)&l_String_reduceLT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_String_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(83, 129, 251, 63, 48, 77, 211, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_String_reduceLE___redArg___closed__0 = (const lean_object*)&l_String_reduceLE___redArg___closed__0_value;
static const lean_string_object l_String_reduceLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_String_reduceLE___redArg___closed__1 = (const lean_object*)&l_String_reduceLE___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_String_reduceLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceLE___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceLE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_String_reduceLE___redArg___closed__2 = (const lean_object*)&l_String_reduceLE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_String_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(181, 148, 60, 222, 34, 40, 11, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceGT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_String_reduceGT___redArg___closed__0 = (const lean_object*)&l_String_reduceGT___redArg___closed__0_value;
static const lean_string_object l_String_reduceGT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_String_reduceGT___redArg___closed__1 = (const lean_object*)&l_String_reduceGT___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceGT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceGT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_String_reduceGT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceGT___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceGT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_String_reduceGT___redArg___closed__2 = (const lean_object*)&l_String_reduceGT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_String_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(37, 205, 223, 144, 3, 26, 41, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceGE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_String_reduceGE___redArg___closed__0 = (const lean_object*)&l_String_reduceGE___redArg___closed__0_value;
static const lean_string_object l_String_reduceGE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_String_reduceGE___redArg___closed__1 = (const lean_object*)&l_String_reduceGE___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceGE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceGE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_String_reduceGE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceGE___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceGE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_String_reduceGE___redArg___closed__2 = (const lean_object*)&l_String_reduceGE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_String_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(192, 35, 33, 237, 211, 197, 6, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_String_reduceEq___redArg___closed__0 = (const lean_object*)&l_String_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_String_reduceEq___redArg___closed__1 = (const lean_object*)&l_String_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(226, 50, 245, 26, 30, 117, 229, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_String_reduceNe___redArg___closed__0 = (const lean_object*)&l_String_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_String_reduceNe___redArg___closed__1 = (const lean_object*)&l_String_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(145, 120, 208, 42, 84, 100, 108, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_String_reduceBEq___redArg___closed__0 = (const lean_object*)&l_String_reduceBEq___redArg___closed__0_value;
static const lean_string_object l_String_reduceBEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_String_reduceBEq___redArg___closed__1 = (const lean_object*)&l_String_reduceBEq___redArg___closed__1_value;
static const lean_ctor_object l_String_reduceBEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceBEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_String_reduceBEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_reduceBEq___redArg___closed__2_value_aux_0),((lean_object*)&l_String_reduceBEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_String_reduceBEq___redArg___closed__2 = (const lean_object*)&l_String_reduceBEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(78, 160, 87, 2, 82, 78, 3, 125)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_String_reduceBNe___redArg___closed__0 = (const lean_object*)&l_String_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_String_reduceBNe___redArg___closed__1 = (const lean_object*)&l_String_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(240, 216, 47, 194, 46, 141, 155, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___redArg(lean_object* v_e_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Meta_getStringValue_x3f(v_e_1_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___redArg___boxed(lean_object* v_e_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_String_fromExpr_x3f___redArg(v_e_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_String_fromExpr_x3f(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_String_fromExpr_x3f___redArg(v_e_8_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___boxed(lean_object* v_e_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_String_fromExpr_x3f(v_e_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg(lean_object* v_e_35_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_37_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__2));
v___x_38_ = lean_unsigned_to_nat(6u);
v___x_39_ = l_Lean_Expr_isAppOfArity(v_e_35_, v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_78_; 
v___x_42_ = l_Lean_Expr_appFn_x21(v_e_35_);
v___x_43_ = l_Lean_Expr_appArg_x21(v___x_42_);
lean_dec_ref(v___x_42_);
v___x_44_ = l_String_fromExpr_x3f___redArg(v___x_43_);
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_78_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_78_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_78_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
if (lean_obj_tag(v_a_45_) == 1)
{
lean_object* v_val_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_73_; 
lean_del_object(v___x_47_);
v_val_49_ = lean_ctor_get(v_a_45_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v_a_45_);
v___x_50_ = l_Lean_Expr_appArg_x21(v_e_35_);
v___x_51_ = l_String_fromExpr_x3f___redArg(v___x_50_);
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
v___x_60_ = lean_string_append(v_val_49_, v_val_56_);
lean_dec(v_val_56_);
v___x_61_ = l_Lean_mkStrLit(v___x_60_);
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
lean_dec(v_val_49_);
v___x_69_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
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
lean_object* v___x_74_; lean_object* v___x_76_; 
lean_dec(v_a_45_);
v___x_74_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_74_);
v___x_76_ = v___x_47_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg___boxed(lean_object* v_e_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_String_reduceAppend___redArg(v_e_79_);
lean_dec_ref(v_e_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend(lean_object* v_e_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_String_reduceAppend___redArg(v_e_82_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___boxed(lean_object* v_e_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_String_reduceAppend(v_e_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_e_92_);
return v_res_101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_115_ = lean_box(0);
v___x_116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_118_ = lean_unsigned_to_nat(7u);
v___x_119_ = lean_mk_empty_array_with_capacity(v___x_118_);
v___x_120_ = lean_array_push(v___x_119_, v___x_117_);
v___x_121_ = lean_array_push(v___x_120_, v___x_116_);
v___x_122_ = lean_array_push(v___x_121_, v___x_116_);
v___x_123_ = lean_array_push(v___x_122_, v___x_116_);
v___x_124_ = lean_array_push(v___x_123_, v___x_115_);
v___x_125_ = lean_array_push(v___x_124_, v___x_115_);
v___x_126_ = lean_array_push(v___x_125_, v___x_115_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_);
v___x_130_ = lean_alloc_closure((void*)(l_String_reduceAppend___boxed), 9, 0);
v___x_131_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_128_, v___x_129_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19____boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
return v_res_133_;
}
}
static lean_object* _init_l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_alloc_closure((void*)(l_String_reduceAppend___boxed), 9, 0);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_138_ = 1;
v___x_139_ = lean_obj_once(&l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_, &l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once, _init_l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_);
v___x_140_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_137_, v___x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21____boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_145_ = 1;
v___x_146_ = lean_obj_once(&l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_, &l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once, _init_l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_);
v___x_147_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_144_, v___x_145_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23____boxed(lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(lean_object* v_e_159_, lean_object* v_s_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2));
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = l_Lean_Expr_isAppOfArity(v_e_159_, v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4));
v___x_170_ = lean_unsigned_to_nat(3u);
v___x_171_ = l_Lean_Expr_isAppOfArity(v_e_159_, v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_s_160_);
lean_dec_ref(v_e_159_);
v___x_172_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = l_Lean_Expr_appFn_x21(v_e_159_);
v___x_175_ = l_Lean_Expr_appArg_x21(v___x_174_);
lean_dec_ref(v___x_174_);
lean_inc(v_a_164_);
lean_inc_ref(v_a_163_);
lean_inc(v_a_162_);
lean_inc_ref(v_a_161_);
v___x_176_ = l_Lean_Meta_getCharValue_x3f(v___x_175_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_190_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_190_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_190_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_190_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
if (lean_obj_tag(v_a_177_) == 1)
{
lean_object* v_val_181_; lean_object* v___x_182_; uint32_t v___x_183_; lean_object* v___x_184_; 
lean_del_object(v___x_179_);
v_val_181_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_val_181_);
lean_dec_ref(v_a_177_);
v___x_182_ = l_Lean_Expr_appArg_x21(v_e_159_);
lean_dec_ref(v_e_159_);
v___x_183_ = lean_unbox_uint32(v_val_181_);
lean_dec(v_val_181_);
v___x_184_ = lean_string_push(v_s_160_, v___x_183_);
v_e_159_ = v___x_182_;
v_s_160_ = v___x_184_;
goto _start;
}
else
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_dec(v_a_177_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_s_160_);
lean_dec_ref(v_e_159_);
v___x_186_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_186_);
v___x_188_ = v___x_179_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_s_160_);
lean_dec_ref(v_e_159_);
v_a_191_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_176_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_176_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_e_159_);
v___x_199_ = l_Lean_mkStrLit(v_s_160_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___boxed(lean_object* v_e_202_, lean_object* v_s_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(v_e_202_, v_s_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(lean_object* v_e_210_, lean_object* v_s_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(v_e_210_, v_s_211_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___boxed(lean_object* v_e_221_, lean_object* v_s_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(v_e_221_, v_s_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___redArg(lean_object* v_e_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = ((lean_object*)(l_String_reduceOfList___redArg___closed__1));
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = l_Lean_Expr_isAppOfArity(v_e_237_, v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
v___x_246_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = l_Lean_Expr_appArg_x21(v_e_237_);
v___x_249_ = ((lean_object*)(l_String_reduceOfList___redArg___closed__2));
v___x_250_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(v___x_248_, v___x_249_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___redArg___boxed(lean_object* v_e_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_String_reduceOfList___redArg(v_e_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_e_251_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList(lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_String_reduceOfList___redArg(v_e_258_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___boxed(lean_object* v_e_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_String_reduceOfList(v_e_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_e_268_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_));
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_));
v___x_294_ = lean_alloc_closure((void*)(l_String_reduceOfList___boxed), 9, 0);
v___x_295_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_292_, v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13____boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_();
return v_res_297_;
}
}
static lean_object* _init_l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_alloc_closure((void*)(l_String_reduceOfList___boxed), 9, 0);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_));
v___x_302_ = 1;
v___x_303_ = lean_obj_once(&l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_, &l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once, _init_l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_);
v___x_304_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_301_, v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15____boxed(lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_));
v___x_309_ = 1;
v___x_310_ = lean_obj_once(&l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_, &l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once, _init_l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_);
v___x_311_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_308_, v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17____boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
return v_res_313_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
v___x_320_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2));
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(lean_object* v_nilFn_322_, lean_object* v_consFn_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_dec_ref(v_consFn_323_);
lean_inc_ref(v_nilFn_322_);
return v_nilFn_322_;
}
else
{
lean_object* v_head_325_; lean_object* v_tail_326_; lean_object* v___x_327_; uint32_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_head_325_ = lean_ctor_get(v_x_324_, 0);
v_tail_326_ = lean_ctor_get(v_x_324_, 1);
v___x_327_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3);
v___x_328_ = lean_unbox_uint32(v_head_325_);
v___x_329_ = lean_uint32_to_nat(v___x_328_);
v___x_330_ = l_Lean_mkRawNatLit(v___x_329_);
v___x_331_ = l_Lean_Expr_app___override(v___x_327_, v___x_330_);
lean_inc_ref(v_consFn_323_);
v___x_332_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(v_nilFn_322_, v_consFn_323_, v_tail_326_);
v___x_333_ = l_Lean_mkAppB(v_consFn_323_, v___x_331_, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___boxed(lean_object* v_nilFn_334_, lean_object* v_consFn_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(v_nilFn_334_, v_consFn_335_, v_x_336_);
lean_dec(v_x_336_);
lean_dec_ref(v_nilFn_334_);
return v_res_337_;
}
}
static lean_object* _init_l_String_reduceToList___redArg___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_box(0);
v___x_345_ = ((lean_object*)(l_String_reduceToList___redArg___closed__2));
v___x_346_ = l_Lean_mkConst(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_String_reduceToList___redArg___closed__5(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((lean_object*)(l_String_reduceToList___redArg___closed__4));
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2));
v___x_352_ = l_Lean_mkConst(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_String_reduceToList___redArg___closed__6(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_nil_355_; 
v___x_353_ = lean_obj_once(&l_String_reduceToList___redArg___closed__3, &l_String_reduceToList___redArg___closed__3_once, _init_l_String_reduceToList___redArg___closed__3);
v___x_354_ = lean_obj_once(&l_String_reduceToList___redArg___closed__5, &l_String_reduceToList___redArg___closed__5_once, _init_l_String_reduceToList___redArg___closed__5);
v_nil_355_ = l_Lean_Expr_app___override(v___x_354_, v___x_353_);
return v_nil_355_;
}
}
static lean_object* _init_l_String_reduceToList___redArg___closed__7(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((lean_object*)(l_String_reduceToList___redArg___closed__4));
v___x_357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4));
v___x_358_ = l_Lean_mkConst(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_String_reduceToList___redArg___closed__8(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_cons_361_; 
v___x_359_ = lean_obj_once(&l_String_reduceToList___redArg___closed__3, &l_String_reduceToList___redArg___closed__3_once, _init_l_String_reduceToList___redArg___closed__3);
v___x_360_ = lean_obj_once(&l_String_reduceToList___redArg___closed__7, &l_String_reduceToList___redArg___closed__7_once, _init_l_String_reduceToList___redArg___closed__7);
v_cons_361_ = l_Lean_Expr_app___override(v___x_360_, v___x_359_);
return v_cons_361_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___redArg(lean_object* v_e_362_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_364_ = ((lean_object*)(l_String_reduceToList___redArg___closed__1));
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = l_Lean_Expr_isAppOfArity(v_e_362_, v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_394_; 
v___x_369_ = l_Lean_Expr_appArg_x21(v_e_362_);
v___x_370_ = l_String_fromExpr_x3f___redArg(v___x_369_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_394_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_394_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_394_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
if (lean_obj_tag(v_a_371_) == 1)
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_389_; 
v_val_375_ = lean_ctor_get(v_a_371_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_a_371_);
if (v_isSharedCheck_389_ == 0)
{
v___x_377_ = v_a_371_;
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v_a_371_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v_nil_379_; lean_object* v_cons_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v_nil_379_ = lean_obj_once(&l_String_reduceToList___redArg___closed__6, &l_String_reduceToList___redArg___closed__6_once, _init_l_String_reduceToList___redArg___closed__6);
v_cons_380_ = lean_obj_once(&l_String_reduceToList___redArg___closed__8, &l_String_reduceToList___redArg___closed__8_once, _init_l_String_reduceToList___redArg___closed__8);
v___x_381_ = lean_string_data(v_val_375_);
v___x_382_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(v_nil_379_, v_cons_380_, v___x_381_);
lean_dec(v___x_381_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 0);
lean_ctor_set(v___x_377_, 0, v___x_382_);
v___x_384_ = v___x_377_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_384_);
v___x_386_ = v___x_373_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_392_; 
lean_dec(v_a_371_);
v___x_390_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_390_);
v___x_392_ = v___x_373_;
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
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___redArg___boxed(lean_object* v_e_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_String_reduceToList___redArg(v_e_395_);
lean_dec_ref(v_e_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList(lean_object* v_e_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_String_reduceToList___redArg(v_e_398_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___boxed(lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_String_reduceToList(v_e_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_e_408_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_));
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_));
v___x_434_ = lean_alloc_closure((void*)(l_String_reduceToList___boxed), 9, 0);
v___x_435_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_432_, v___x_433_, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13____boxed(lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_();
return v_res_437_;
}
}
static lean_object* _init_l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_alloc_closure((void*)(l_String_reduceToList___boxed), 9, 0);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_));
v___x_442_ = 1;
v___x_443_ = lean_obj_once(&l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_, &l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once, _init_l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_);
v___x_444_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_));
v___x_449_ = 1;
v___x_450_ = lean_obj_once(&l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_, &l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once, _init_l_String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_);
v___x_451_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_448_, v___x_449_, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17____boxed(lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush___redArg(lean_object* v_e_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_464_ = ((lean_object*)(l_String_reducePush___redArg___closed__1));
v___x_465_ = lean_unsigned_to_nat(2u);
v___x_466_ = l_Lean_Expr_isAppOfArity(v_e_458_, v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
v___x_467_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_514_; 
v___x_469_ = l_Lean_Expr_appFn_x21(v_e_458_);
v___x_470_ = l_Lean_Expr_appArg_x21(v___x_469_);
lean_dec_ref(v___x_469_);
v___x_471_ = l_String_fromExpr_x3f___redArg(v___x_470_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_514_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_514_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_514_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 1)
{
lean_object* v_val_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_del_object(v___x_474_);
v_val_476_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v_a_472_);
v___x_477_ = l_Lean_Expr_appArg_x21(v_e_458_);
v___x_478_ = l_Lean_Meta_getCharValue_x3f(v___x_477_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_501_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_501_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_501_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_501_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
if (lean_obj_tag(v_a_479_) == 1)
{
lean_object* v_val_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_496_; 
v_val_483_ = lean_ctor_get(v_a_479_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_496_ == 0)
{
v___x_485_ = v_a_479_;
v_isShared_486_ = v_isSharedCheck_496_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_val_483_);
lean_dec(v_a_479_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_496_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint32_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_487_ = lean_unbox_uint32(v_val_483_);
lean_dec(v_val_483_);
v___x_488_ = lean_string_push(v_val_476_, v___x_487_);
v___x_489_ = l_Lean_mkStrLit(v___x_488_);
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 0);
lean_ctor_set(v___x_485_, 0, v___x_489_);
v___x_491_ = v___x_485_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_491_);
v___x_493_ = v___x_481_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_a_479_);
lean_dec(v_val_476_);
v___x_497_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_497_);
v___x_499_ = v___x_481_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_val_476_);
v_a_502_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_478_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_478_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_dec(v_a_472_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
v___x_510_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_510_);
v___x_512_ = v___x_474_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reducePush___redArg___boxed(lean_object* v_e_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_String_reducePush___redArg(v_e_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec_ref(v_e_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush(lean_object* v_e_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_String_reducePush___redArg(v_e_522_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush___boxed(lean_object* v_e_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_String_reducePush(v_e_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_e_532_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_));
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_));
v___x_559_ = lean_alloc_closure((void*)(l_String_reducePush___boxed), 9, 0);
v___x_560_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_557_, v___x_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14____boxed(lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_();
return v_res_562_;
}
}
static lean_object* _init_l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_alloc_closure((void*)(l_String_reducePush___boxed), 9, 0);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_));
v___x_567_ = 1;
v___x_568_ = lean_obj_once(&l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_, &l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once, _init_l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_);
v___x_569_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_566_, v___x_567_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16____boxed(lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_));
v___x_574_ = 1;
v___x_575_ = lean_obj_once(&l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_, &l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once, _init_l_String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_);
v___x_576_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_573_, v___x_574_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18____boxed(lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___redArg(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = ((lean_object*)(l_String_reduceSingleton___redArg___closed__1));
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = l_Lean_Expr_isAppOfArity(v_e_583_, v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
v___x_592_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_Expr_appArg_x21(v_e_583_);
v___x_595_ = l_Lean_Meta_getCharValue_x3f(v___x_594_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_619_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_619_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
if (lean_obj_tag(v_a_596_) == 1)
{
lean_object* v_val_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_614_; 
v_val_600_ = lean_ctor_get(v_a_596_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_602_ = v_a_596_;
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_val_600_);
lean_dec(v_a_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; uint32_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_604_ = ((lean_object*)(l_String_reduceOfList___redArg___closed__2));
v___x_605_ = lean_unbox_uint32(v_val_600_);
lean_dec(v_val_600_);
v___x_606_ = lean_string_push(v___x_604_, v___x_605_);
v___x_607_ = l_Lean_mkStrLit(v___x_606_);
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 0);
lean_ctor_set(v___x_602_, 0, v___x_607_);
v___x_609_ = v___x_602_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_609_);
v___x_611_ = v___x_598_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
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
lean_object* v___x_615_; lean_object* v___x_617_; 
lean_dec(v_a_596_);
v___x_615_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_615_);
v___x_617_ = v___x_598_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_595_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_595_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___redArg___boxed(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_String_reduceSingleton___redArg(v_e_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec_ref(v_e_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_String_reduceSingleton___redArg(v_e_635_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___boxed(lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_String_reduceSingleton(v_e_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_e_645_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_));
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_));
v___x_671_ = lean_alloc_closure((void*)(l_String_reduceSingleton___boxed), 9, 0);
v___x_672_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_669_, v___x_670_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13____boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_();
return v_res_674_;
}
}
static lean_object* _init_l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_alloc_closure((void*)(l_String_reduceSingleton___boxed), 9, 0);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_));
v___x_679_ = 1;
v___x_680_ = lean_obj_once(&l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_, &l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once, _init_l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_);
v___x_681_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_678_, v___x_679_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15____boxed(lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_));
v___x_686_ = 1;
v___x_687_ = lean_obj_once(&l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_, &l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once, _init_l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_);
v___x_688_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_685_, v___x_686_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17____boxed(lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg(lean_object* v_declName_693_, lean_object* v_arity_694_, lean_object* v_op_695_, lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_Expr_isAppOfArity(v_e_696_, v_declName_693_, v_arity_694_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_e_696_);
lean_dec_ref(v_op_695_);
v___x_703_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_732_; 
v___x_705_ = l_Lean_Expr_appFn_x21(v_e_696_);
v___x_706_ = l_Lean_Expr_appArg_x21(v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = l_String_fromExpr_x3f___redArg(v___x_706_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_732_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_732_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_732_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
if (lean_obj_tag(v_a_708_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_727_; 
lean_del_object(v___x_710_);
v_val_712_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_val_712_);
lean_dec_ref(v_a_708_);
v___x_713_ = l_Lean_Expr_appArg_x21(v_e_696_);
v___x_714_ = l_String_fromExpr_x3f___redArg(v___x_713_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_727_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; 
lean_del_object(v___x_717_);
v_val_719_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_val_719_);
lean_dec_ref(v_a_715_);
v___x_720_ = lean_apply_2(v_op_695_, v_val_712_, v_val_719_);
v___x_721_ = lean_unbox(v___x_720_);
v___x_722_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_696_, v___x_721_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_a_715_);
lean_dec(v_val_712_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_e_696_);
lean_dec_ref(v_op_695_);
v___x_723_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_723_);
v___x_725_ = v___x_717_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec(v_a_708_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_e_696_);
lean_dec_ref(v_op_695_);
v___x_728_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_728_);
v___x_730_ = v___x_710_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg___boxed(lean_object* v_declName_733_, lean_object* v_arity_734_, lean_object* v_op_735_, lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_String_reduceBinPred___redArg(v_declName_733_, v_arity_734_, v_op_735_, v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_declName_733_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred(lean_object* v_declName_743_, lean_object* v_arity_744_, lean_object* v_op_745_, lean_object* v_e_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = l_Lean_Expr_isAppOfArity(v_e_746_, v_declName_743_, v_arity_744_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_e_746_);
lean_dec_ref(v_op_745_);
v___x_756_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_785_; 
v___x_758_ = l_Lean_Expr_appFn_x21(v_e_746_);
v___x_759_ = l_Lean_Expr_appArg_x21(v___x_758_);
lean_dec_ref(v___x_758_);
v___x_760_ = l_String_fromExpr_x3f___redArg(v___x_759_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_785_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_785_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_785_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
if (lean_obj_tag(v_a_761_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_763_);
v_val_765_ = lean_ctor_get(v_a_761_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v_a_761_);
v___x_766_ = l_Lean_Expr_appArg_x21(v_e_746_);
v___x_767_ = l_String_fromExpr_x3f___redArg(v___x_766_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_780_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
if (lean_obj_tag(v_a_768_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; 
lean_del_object(v___x_770_);
v_val_772_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v_a_768_);
v___x_773_ = lean_apply_2(v_op_745_, v_val_765_, v_val_772_);
v___x_774_ = lean_unbox(v___x_773_);
v___x_775_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_746_, v___x_774_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec(v_a_768_);
lean_dec(v_val_765_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_e_746_);
lean_dec_ref(v_op_745_);
v___x_776_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_776_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_a_761_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_e_746_);
lean_dec_ref(v_op_745_);
v___x_781_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_781_);
v___x_783_ = v___x_763_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___boxed(lean_object* v_declName_786_, lean_object* v_arity_787_, lean_object* v_op_788_, lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_String_reduceBinPred(v_declName_786_, v_arity_787_, v_op_788_, v_e_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec(v_declName_786_);
return v_res_798_;
}
}
static lean_object* _init_l_String_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_box(0);
v___x_805_ = ((lean_object*)(l_String_reduceBoolPred___redArg___closed__2));
v___x_806_ = l_Lean_mkConst(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l_String_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_box(0);
v___x_812_ = ((lean_object*)(l_String_reduceBoolPred___redArg___closed__5));
v___x_813_ = l_Lean_mkConst(v___x_812_, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg(lean_object* v_declName_814_, lean_object* v_arity_815_, lean_object* v_op_816_, lean_object* v_e_817_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Expr_isAppOfArity(v_e_817_, v_declName_814_, v_arity_815_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref(v_op_816_);
v___x_820_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_862_; 
v___x_822_ = l_Lean_Expr_appFn_x21(v_e_817_);
v___x_823_ = l_Lean_Expr_appArg_x21(v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = l_String_fromExpr_x3f___redArg(v___x_823_);
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_862_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_862_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_862_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
if (lean_obj_tag(v_a_825_) == 1)
{
lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_857_; 
v_val_829_ = lean_ctor_get(v_a_825_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_857_ == 0)
{
v___x_831_ = v_a_825_;
v_isShared_832_ = v_isSharedCheck_857_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_dec(v_a_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_857_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_856_; 
v___x_833_ = l_Lean_Expr_appArg_x21(v_e_817_);
v___x_834_ = l_String_fromExpr_x3f___redArg(v___x_833_);
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_856_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_856_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_856_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___y_840_; 
if (lean_obj_tag(v_a_835_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
lean_del_object(v___x_827_);
v_val_847_ = lean_ctor_get(v_a_835_, 0);
lean_inc(v_val_847_);
lean_dec_ref(v_a_835_);
v___x_848_ = lean_apply_2(v_op_816_, v_val_829_, v_val_847_);
v___x_849_ = lean_unbox(v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_840_ = v___x_850_;
goto v___jp_839_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_840_ = v___x_851_;
goto v___jp_839_;
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_del_object(v___x_837_);
lean_dec(v_a_835_);
lean_del_object(v___x_831_);
lean_dec(v_val_829_);
lean_dec_ref(v_op_816_);
v___x_852_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_852_);
v___x_854_ = v___x_827_;
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
v___jp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___y_840_);
v___x_842_ = v___x_831_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___y_840_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_842_);
v___x_844_ = v___x_837_;
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
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_a_825_);
lean_dec_ref(v_op_816_);
v___x_858_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_858_);
v___x_860_ = v___x_827_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg___boxed(lean_object* v_declName_863_, lean_object* v_arity_864_, lean_object* v_op_865_, lean_object* v_e_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_String_reduceBoolPred___redArg(v_declName_863_, v_arity_864_, v_op_865_, v_e_866_);
lean_dec_ref(v_e_866_);
lean_dec(v_declName_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred(lean_object* v_declName_869_, lean_object* v_arity_870_, lean_object* v_op_871_, lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = l_Lean_Expr_isAppOfArity(v_e_872_, v_declName_869_, v_arity_870_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref(v_op_871_);
v___x_882_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_924_; 
v___x_884_ = l_Lean_Expr_appFn_x21(v_e_872_);
v___x_885_ = l_Lean_Expr_appArg_x21(v___x_884_);
lean_dec_ref(v___x_884_);
v___x_886_ = l_String_fromExpr_x3f___redArg(v___x_885_);
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_924_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_924_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_924_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
if (lean_obj_tag(v_a_887_) == 1)
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_919_; 
v_val_891_ = lean_ctor_get(v_a_887_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_919_ == 0)
{
v___x_893_ = v_a_887_;
v_isShared_894_ = v_isSharedCheck_919_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v_a_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_919_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_918_; 
v___x_895_ = l_Lean_Expr_appArg_x21(v_e_872_);
v___x_896_ = l_String_fromExpr_x3f___redArg(v___x_895_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_918_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_918_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_918_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___y_902_; 
if (lean_obj_tag(v_a_897_) == 1)
{
lean_object* v_val_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
lean_del_object(v___x_889_);
v_val_909_ = lean_ctor_get(v_a_897_, 0);
lean_inc(v_val_909_);
lean_dec_ref(v_a_897_);
v___x_910_ = lean_apply_2(v_op_871_, v_val_891_, v_val_909_);
v___x_911_ = lean_unbox(v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_902_ = v___x_912_;
goto v___jp_901_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_902_ = v___x_913_;
goto v___jp_901_;
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_del_object(v___x_899_);
lean_dec(v_a_897_);
lean_del_object(v___x_893_);
lean_dec(v_val_891_);
lean_dec_ref(v_op_871_);
v___x_914_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_914_);
v___x_916_ = v___x_889_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
v___jp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 0);
lean_ctor_set(v___x_893_, 0, v___y_902_);
v___x_904_ = v___x_893_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___y_902_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_904_);
v___x_906_ = v___x_899_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v_a_887_);
lean_dec_ref(v_op_871_);
v___x_920_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_920_);
v___x_922_ = v___x_889_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___boxed(lean_object* v_declName_925_, lean_object* v_arity_926_, lean_object* v_op_927_, lean_object* v_e_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_String_reduceBoolPred(v_declName_925_, v_arity_926_, v_op_927_, v_e_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_e_928_);
lean_dec(v_declName_925_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___redArg(lean_object* v_e_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = ((lean_object*)(l_String_reduceLT___redArg___closed__2));
v___x_950_ = lean_unsigned_to_nat(4u);
v___x_951_ = l_Lean_Expr_isAppOfArity(v_e_943_, v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec_ref(v_e_943_);
v___x_952_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_980_; 
v___x_954_ = l_Lean_Expr_appFn_x21(v_e_943_);
v___x_955_ = l_Lean_Expr_appArg_x21(v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = l_String_fromExpr_x3f___redArg(v___x_955_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_980_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_980_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_980_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
if (lean_obj_tag(v_a_957_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_959_);
v_val_961_ = lean_ctor_get(v_a_957_, 0);
lean_inc(v_val_961_);
lean_dec_ref(v_a_957_);
v___x_962_ = l_Lean_Expr_appArg_x21(v_e_943_);
v___x_963_ = l_String_fromExpr_x3f___redArg(v___x_962_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_975_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
if (lean_obj_tag(v_a_964_) == 1)
{
lean_object* v_val_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
lean_del_object(v___x_966_);
v_val_968_ = lean_ctor_get(v_a_964_, 0);
lean_inc(v_val_968_);
lean_dec_ref(v_a_964_);
v___x_969_ = lean_string_dec_lt(v_val_961_, v_val_968_);
lean_dec(v_val_968_);
lean_dec(v_val_961_);
v___x_970_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_943_, v___x_969_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec(v_a_964_);
lean_dec(v_val_961_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec_ref(v_e_943_);
v___x_971_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_971_);
v___x_973_ = v___x_966_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
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
else
{
lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_a_957_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec_ref(v_e_943_);
v___x_976_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_976_);
v___x_978_ = v___x_959_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___redArg___boxed(lean_object* v_e_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_String_reduceLT___redArg(v_e_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT(lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_String_reduceLT___redArg(v_e_988_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___boxed(lean_object* v_e_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_String_reduceLT(v_e_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1028_ = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
v___x_1029_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1026_, v___x_1027_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20____boxed(lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
return v_res_1031_;
}
}
static lean_object* _init_l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1036_ = 1;
v___x_1037_ = lean_obj_once(&l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_, &l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once, _init_l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_);
v___x_1038_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1035_, v___x_1036_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22____boxed(lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1043_ = 1;
v___x_1044_ = lean_obj_once(&l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_, &l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once, _init_l_String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_);
v___x_1045_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1042_, v___x_1043_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24____boxed(lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___redArg(lean_object* v_e_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = ((lean_object*)(l_String_reduceLE___redArg___closed__2));
v___x_1060_ = lean_unsigned_to_nat(4u);
v___x_1061_ = l_Lean_Expr_isAppOfArity(v_e_1053_, v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_e_1053_);
v___x_1062_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1090_; 
v___x_1064_ = l_Lean_Expr_appFn_x21(v_e_1053_);
v___x_1065_ = l_Lean_Expr_appArg_x21(v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_String_fromExpr_x3f___redArg(v___x_1065_);
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1090_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1090_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 1)
{
lean_object* v_val_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_1069_);
v_val_1071_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_val_1071_);
lean_dec_ref(v_a_1067_);
v___x_1072_ = l_Lean_Expr_appArg_x21(v_e_1053_);
v___x_1073_ = l_String_fromExpr_x3f___redArg(v___x_1072_);
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
if (lean_obj_tag(v_a_1074_) == 1)
{
lean_object* v_val_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; 
lean_del_object(v___x_1076_);
v_val_1078_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_val_1078_);
lean_dec_ref(v_a_1074_);
v___x_1079_ = l_String_decLE(v_val_1071_, v_val_1078_);
lean_dec(v_val_1078_);
lean_dec(v_val_1071_);
v___x_1080_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1053_, v___x_1079_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_dec(v_a_1074_);
lean_dec(v_val_1071_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_e_1053_);
v___x_1081_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1081_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec(v_a_1067_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_e_1053_);
v___x_1086_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1086_);
v___x_1088_ = v___x_1069_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___redArg___boxed(lean_object* v_e_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_String_reduceLE___redArg(v_e_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE(lean_object* v_e_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_String_reduceLE___redArg(v_e_1098_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___boxed(lean_object* v_e_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_String_reduceLE(v_e_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1138_ = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
v___x_1139_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1136_, v___x_1137_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20____boxed(lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
return v_res_1141_;
}
}
static lean_object* _init_l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1146_ = 1;
v___x_1147_ = lean_obj_once(&l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_, &l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once, _init_l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_);
v___x_1148_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1145_, v___x_1146_, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22____boxed(lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1153_ = 1;
v___x_1154_ = lean_obj_once(&l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_, &l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once, _init_l_String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_);
v___x_1155_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1152_, v___x_1153_, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24____boxed(lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___redArg(lean_object* v_e_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = ((lean_object*)(l_String_reduceGT___redArg___closed__2));
v___x_1170_ = lean_unsigned_to_nat(4u);
v___x_1171_ = l_Lean_Expr_isAppOfArity(v_e_1163_, v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_e_1163_);
v___x_1172_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1200_; 
v___x_1174_ = l_Lean_Expr_appFn_x21(v_e_1163_);
v___x_1175_ = l_Lean_Expr_appArg_x21(v___x_1174_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = l_String_fromExpr_x3f___redArg(v___x_1175_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1200_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1200_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
if (lean_obj_tag(v_a_1177_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1195_; 
lean_del_object(v___x_1179_);
v_val_1181_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_val_1181_);
lean_dec_ref(v_a_1177_);
v___x_1182_ = l_Lean_Expr_appArg_x21(v_e_1163_);
v___x_1183_ = l_String_fromExpr_x3f___redArg(v___x_1182_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1195_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1195_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
if (lean_obj_tag(v_a_1184_) == 1)
{
lean_object* v_val_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
lean_del_object(v___x_1186_);
v_val_1188_ = lean_ctor_get(v_a_1184_, 0);
lean_inc(v_val_1188_);
lean_dec_ref(v_a_1184_);
v___x_1189_ = lean_string_dec_lt(v_val_1188_, v_val_1181_);
lean_dec(v_val_1181_);
lean_dec(v_val_1188_);
v___x_1190_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1163_, v___x_1189_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_dec(v_a_1184_);
lean_dec(v_val_1181_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_e_1163_);
v___x_1191_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1191_);
v___x_1193_ = v___x_1186_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_dec(v_a_1177_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_e_1163_);
v___x_1196_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1196_);
v___x_1198_ = v___x_1179_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___redArg___boxed(lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_String_reduceGT___redArg(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT(lean_object* v_e_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_String_reduceGT___redArg(v_e_1208_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___boxed(lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_String_reduceGT(v_e_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_));
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1235_ = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
v___x_1236_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1233_, v___x_1234_, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20____boxed(lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
return v_res_1238_;
}
}
static lean_object* _init_l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_));
v___x_1243_ = 1;
v___x_1244_ = lean_obj_once(&l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_, &l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once, _init_l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_);
v___x_1245_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1242_, v___x_1243_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22____boxed(lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_));
v___x_1250_ = 1;
v___x_1251_ = lean_obj_once(&l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_, &l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once, _init_l_String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_);
v___x_1252_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1249_, v___x_1250_, v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24____boxed(lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___redArg(lean_object* v_e_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = ((lean_object*)(l_String_reduceGE___redArg___closed__2));
v___x_1267_ = lean_unsigned_to_nat(4u);
v___x_1268_ = l_Lean_Expr_isAppOfArity(v_e_1260_, v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_e_1260_);
v___x_1269_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1297_; 
v___x_1271_ = l_Lean_Expr_appFn_x21(v_e_1260_);
v___x_1272_ = l_Lean_Expr_appArg_x21(v___x_1271_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_String_fromExpr_x3f___redArg(v___x_1272_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1297_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1297_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_a_1274_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1276_);
v_val_1278_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_val_1278_);
lean_dec_ref(v_a_1274_);
v___x_1279_ = l_Lean_Expr_appArg_x21(v_e_1260_);
v___x_1280_ = l_String_fromExpr_x3f___redArg(v___x_1279_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
if (lean_obj_tag(v_a_1281_) == 1)
{
lean_object* v_val_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1283_);
v_val_1285_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_val_1285_);
lean_dec_ref(v_a_1281_);
v___x_1286_ = l_String_decLE(v_val_1285_, v_val_1278_);
lean_dec(v_val_1278_);
lean_dec(v_val_1285_);
v___x_1287_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1260_, v___x_1286_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_dec(v_a_1281_);
lean_dec(v_val_1278_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_e_1260_);
v___x_1288_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1288_);
v___x_1290_ = v___x_1283_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
lean_dec(v_a_1274_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_e_1260_);
v___x_1293_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1293_);
v___x_1295_ = v___x_1276_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___redArg___boxed(lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_String_reduceGE___redArg(v_e_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE(lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_String_reduceGE___redArg(v_e_1305_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___boxed(lean_object* v_e_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_String_reduceGE(v_e_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_));
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1332_ = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
v___x_1333_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1330_, v___x_1331_, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20____boxed(lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
return v_res_1335_;
}
}
static lean_object* _init_l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_));
v___x_1340_ = 1;
v___x_1341_ = lean_obj_once(&l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_, &l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once, _init_l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_);
v___x_1342_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1339_, v___x_1340_, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22____boxed(lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_));
v___x_1347_ = 1;
v___x_1348_ = lean_obj_once(&l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_, &l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once, _init_l_String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_);
v___x_1349_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1346_, v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24____boxed(lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___redArg(lean_object* v_e_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = ((lean_object*)(l_String_reduceEq___redArg___closed__1));
v___x_1362_ = lean_unsigned_to_nat(3u);
v___x_1363_ = l_Lean_Expr_isAppOfArity(v_e_1355_, v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec_ref(v_e_1355_);
v___x_1364_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1392_; 
v___x_1366_ = l_Lean_Expr_appFn_x21(v_e_1355_);
v___x_1367_ = l_Lean_Expr_appArg_x21(v___x_1366_);
lean_dec_ref(v___x_1366_);
v___x_1368_ = l_String_fromExpr_x3f___redArg(v___x_1367_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1392_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1392_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
if (lean_obj_tag(v_a_1369_) == 1)
{
lean_object* v_val_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1387_; 
lean_del_object(v___x_1371_);
v_val_1373_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_val_1373_);
lean_dec_ref(v_a_1369_);
v___x_1374_ = l_Lean_Expr_appArg_x21(v_e_1355_);
v___x_1375_ = l_String_fromExpr_x3f___redArg(v___x_1374_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1387_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1387_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
if (lean_obj_tag(v_a_1376_) == 1)
{
lean_object* v_val_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1378_);
v_val_1380_ = lean_ctor_get(v_a_1376_, 0);
lean_inc(v_val_1380_);
lean_dec_ref(v_a_1376_);
v___x_1381_ = lean_string_dec_eq(v_val_1373_, v_val_1380_);
lean_dec(v_val_1380_);
lean_dec(v_val_1373_);
v___x_1382_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1355_, v___x_1381_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec(v_a_1376_);
lean_dec(v_val_1373_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec_ref(v_e_1355_);
v___x_1383_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1383_);
v___x_1385_ = v___x_1378_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec(v_a_1369_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec_ref(v_e_1355_);
v___x_1388_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1388_);
v___x_1390_ = v___x_1371_;
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
}
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___redArg___boxed(lean_object* v_e_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_String_reduceEq___redArg(v_e_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq(lean_object* v_e_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_String_reduceEq___redArg(v_e_1400_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___boxed(lean_object* v_e_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_String_reduceEq(v_e_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_));
v___x_1438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_));
v___x_1439_ = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
v___x_1440_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1437_, v___x_1438_, v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20____boxed(lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_();
return v_res_1442_;
}
}
static lean_object* _init_l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_));
v___x_1447_ = 1;
v___x_1448_ = lean_obj_once(&l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_, &l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22__once, _init_l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_);
v___x_1449_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1446_, v___x_1447_, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22____boxed(lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_();
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_));
v___x_1454_ = 1;
v___x_1455_ = lean_obj_once(&l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_, &l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22__once, _init_l_String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_);
v___x_1456_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1453_, v___x_1454_, v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_24____boxed(lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_24_();
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___redArg(lean_object* v_e_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = ((lean_object*)(l_String_reduceNe___redArg___closed__1));
v___x_1469_ = lean_unsigned_to_nat(3u);
v___x_1470_ = l_Lean_Expr_isAppOfArity(v_e_1462_, v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_e_1462_);
v___x_1471_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1501_; 
v___x_1473_ = l_Lean_Expr_appFn_x21(v_e_1462_);
v___x_1474_ = l_Lean_Expr_appArg_x21(v___x_1473_);
lean_dec_ref(v___x_1473_);
v___x_1475_ = l_String_fromExpr_x3f___redArg(v___x_1474_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1501_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1501_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
if (lean_obj_tag(v_a_1476_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1496_; 
lean_del_object(v___x_1478_);
v_val_1480_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_val_1480_);
lean_dec_ref(v_a_1476_);
v___x_1481_ = l_Lean_Expr_appArg_x21(v_e_1462_);
v___x_1482_ = l_String_fromExpr_x3f___redArg(v___x_1481_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1496_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1496_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
if (lean_obj_tag(v_a_1483_) == 1)
{
lean_object* v_val_1487_; uint8_t v___x_1488_; 
lean_del_object(v___x_1485_);
v_val_1487_ = lean_ctor_get(v_a_1483_, 0);
lean_inc(v_val_1487_);
lean_dec_ref(v_a_1483_);
v___x_1488_ = lean_string_dec_eq(v_val_1480_, v_val_1487_);
lean_dec(v_val_1487_);
lean_dec(v_val_1480_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1462_, v___x_1470_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1489_;
}
else
{
uint8_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = 0;
v___x_1491_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1462_, v___x_1490_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1491_;
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_dec(v_a_1483_);
lean_dec(v_val_1480_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_e_1462_);
v___x_1492_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1492_);
v___x_1494_ = v___x_1485_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
lean_dec(v_a_1476_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_e_1462_);
v___x_1497_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1497_);
v___x_1499_ = v___x_1478_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___redArg___boxed(lean_object* v_e_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_String_reduceNe___redArg(v_e_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe(lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_String_reduceNe___redArg(v_e_1509_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___boxed(lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_String_reduceNe(v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_));
v___x_1552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_));
v___x_1553_ = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
v___x_1554_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1551_, v___x_1552_, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20____boxed(lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_();
return v_res_1556_;
}
}
static lean_object* _init_l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_));
v___x_1561_ = 1;
v___x_1562_ = lean_obj_once(&l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_, &l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22__once, _init_l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_);
v___x_1563_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1560_, v___x_1561_, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22____boxed(lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_();
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_));
v___x_1568_ = 1;
v___x_1569_ = lean_obj_once(&l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_, &l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22__once, _init_l_String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_);
v___x_1570_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1567_, v___x_1568_, v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_24____boxed(lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_24_();
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg(lean_object* v_e_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1580_ = ((lean_object*)(l_String_reduceBEq___redArg___closed__2));
v___x_1581_ = lean_unsigned_to_nat(4u);
v___x_1582_ = l_Lean_Expr_isAppOfArity(v_e_1578_, v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1624_; 
v___x_1585_ = l_Lean_Expr_appFn_x21(v_e_1578_);
v___x_1586_ = l_Lean_Expr_appArg_x21(v___x_1585_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = l_String_fromExpr_x3f___redArg(v___x_1586_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1624_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1624_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
if (lean_obj_tag(v_a_1588_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1619_; 
v_val_1592_ = lean_ctor_get(v_a_1588_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1594_ = v_a_1588_;
v_isShared_1595_ = v_isSharedCheck_1619_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_val_1592_);
lean_dec(v_a_1588_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1619_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1618_; 
v___x_1596_ = l_Lean_Expr_appArg_x21(v_e_1578_);
v___x_1597_ = l_String_fromExpr_x3f___redArg(v___x_1596_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1618_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1618_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___y_1603_; 
if (lean_obj_tag(v_a_1598_) == 1)
{
lean_object* v_val_1610_; uint8_t v___x_1611_; 
lean_del_object(v___x_1590_);
v_val_1610_ = lean_ctor_get(v_a_1598_, 0);
lean_inc(v_val_1610_);
lean_dec_ref(v_a_1598_);
v___x_1611_ = lean_string_dec_eq(v_val_1592_, v_val_1610_);
lean_dec(v_val_1610_);
lean_dec(v_val_1592_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_1603_ = v___x_1612_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_1603_ = v___x_1613_;
goto v___jp_1602_;
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
lean_del_object(v___x_1594_);
lean_dec(v_val_1592_);
v___x_1614_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1614_);
v___x_1616_ = v___x_1590_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
v___jp_1602_:
{
lean_object* v___x_1605_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 0, v___y_1603_);
v___x_1605_ = v___x_1594_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___y_1603_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1605_);
v___x_1607_ = v___x_1600_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_dec(v_a_1588_);
v___x_1620_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1620_);
v___x_1622_ = v___x_1590_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
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
}
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg___boxed(lean_object* v_e_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_String_reduceBEq___redArg(v_e_1625_);
lean_dec_ref(v_e_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq(lean_object* v_e_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_String_reduceBEq___redArg(v_e_1628_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___boxed(lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_String_reduceBEq(v_e_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_e_1638_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1668_ = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
v___x_1669_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1666_, v___x_1667_, v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20____boxed(lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
return v_res_1671_;
}
}
static lean_object* _init_l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1676_ = 1;
v___x_1677_ = lean_obj_once(&l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_, &l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once, _init_l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_);
v___x_1678_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1675_, v___x_1676_, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22____boxed(lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1683_ = 1;
v___x_1684_ = lean_obj_once(&l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_, &l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once, _init_l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_);
v___x_1685_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1682_, v___x_1683_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24____boxed(lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg(lean_object* v_e_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_String_reduceBNe___redArg___closed__1));
v___x_1694_ = lean_unsigned_to_nat(4u);
v___x_1695_ = l_Lean_Expr_isAppOfArity(v_e_1691_, v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1738_; 
v___x_1698_ = l_Lean_Expr_appFn_x21(v_e_1691_);
v___x_1699_ = l_Lean_Expr_appArg_x21(v___x_1698_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = l_String_fromExpr_x3f___redArg(v___x_1699_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1738_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1738_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
if (lean_obj_tag(v_a_1701_) == 1)
{
lean_object* v_val_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1733_; 
v_val_1705_ = lean_ctor_get(v_a_1701_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1707_ = v_a_1701_;
v_isShared_1708_ = v_isSharedCheck_1733_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_val_1705_);
lean_dec(v_a_1701_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1733_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1732_; 
v___x_1709_ = l_Lean_Expr_appArg_x21(v_e_1691_);
v___x_1710_ = l_String_fromExpr_x3f___redArg(v___x_1709_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1732_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1732_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___y_1716_; 
if (lean_obj_tag(v_a_1711_) == 1)
{
lean_object* v_val_1725_; uint8_t v___x_1726_; 
lean_del_object(v___x_1703_);
v_val_1725_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_val_1725_);
lean_dec_ref(v_a_1711_);
v___x_1726_ = lean_string_dec_eq(v_val_1705_, v_val_1725_);
lean_dec(v_val_1725_);
lean_dec(v_val_1705_);
if (v___x_1726_ == 0)
{
if (v___x_1695_ == 0)
{
goto v___jp_1723_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_1716_ = v___x_1727_;
goto v___jp_1715_;
}
}
else
{
goto v___jp_1723_;
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_del_object(v___x_1713_);
lean_dec(v_a_1711_);
lean_del_object(v___x_1707_);
lean_dec(v_val_1705_);
v___x_1728_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1728_);
v___x_1730_ = v___x_1703_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
v___jp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1716_);
v___x_1718_ = v___x_1707_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___y_1716_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1718_);
v___x_1720_ = v___x_1713_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
v___jp_1723_:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_1716_ = v___x_1724_;
goto v___jp_1715_;
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_dec(v_a_1701_);
v___x_1734_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1734_);
v___x_1736_ = v___x_1703_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg___boxed(lean_object* v_e_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_String_reduceBNe___redArg(v_e_1739_);
lean_dec_ref(v_e_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe(lean_object* v_e_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_String_reduceBNe___redArg(v_e_1742_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___boxed(lean_object* v_e_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_String_reduceBNe(v_e_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_e_1752_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1782_ = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
v___x_1783_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1780_, v___x_1781_, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20____boxed(lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
return v_res_1785_;
}
}
static lean_object* _init_l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1790_ = 1;
v___x_1791_ = lean_obj_once(&l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_, &l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once, _init_l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_);
v___x_1792_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1789_, v___x_1790_, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22____boxed(lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1797_ = 1;
v___x_1798_ = lean_obj_once(&l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_, &l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once, _init_l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_);
v___x_1799_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1796_, v___x_1797_, v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24____boxed(lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
return v_res_1801_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_810684339____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_731978007____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
}
#ifdef __cplusplus
}
#endif
