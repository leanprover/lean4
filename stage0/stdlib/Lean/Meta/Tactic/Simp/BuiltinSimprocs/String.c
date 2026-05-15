// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.String
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char import Lean.Meta.StringLitProof
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
lean_object* l_Lean_Meta_mkStringLitNeProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalEqPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
uint8_t l_String_decLE(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_evalNePropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17____boxed(lean_object*);
static lean_once_cell_t l_String_reduceToSingleton___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_reduceToSingleton___redArg___closed__0;
LEAN_EXPORT lean_object* l_String_reduceToSingleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToSingleton___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToSingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceToSingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reduceToSingleton"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(188, 114, 101, 196, 232, 204, 81, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(83, 129, 251, 63, 48, 77, 211, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(181, 148, 60, 222, 34, 40, 11, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(37, 205, 223, 144, 3, 26, 41, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(192, 35, 33, 237, 211, 197, 6, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_reduceEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_String_reduceEq___closed__0 = (const lean_object*)&l_String_reduceEq___closed__0_value;
static const lean_ctor_object l_String_reduceEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_String_reduceEq___closed__1 = (const lean_object*)&l_String_reduceEq___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(226, 50, 245, 26, 30, 117, 229, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceEq___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceNe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_String_reduceNe___closed__0 = (const lean_object*)&l_String_reduceNe___closed__0_value;
static const lean_ctor_object l_String_reduceNe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceNe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_String_reduceNe___closed__1 = (const lean_object*)&l_String_reduceNe___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(145, 120, 208, 42, 84, 100, 108, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(78, 160, 87, 2, 82, 78, 3, 125)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_String_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_String_reduceBNe___redArg___closed__0 = (const lean_object*)&l_String_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_String_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_String_reduceBNe___redArg___closed__1 = (const lean_object*)&l_String_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(240, 216, 47, 194, 46, 141, 155, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_String_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_alloc_closure((void*)(l_String_reduceAppend___boxed), 9, 0);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_138_ = 1;
v___x_139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_);
v___x_140_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_137_, v___x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21____boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_));
v___x_145_ = 1;
v___x_146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_);
v___x_147_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_144_, v___x_145_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23____boxed(lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
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
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
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
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
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
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
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
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_alloc_closure((void*)(l_String_reduceOfList___boxed), 9, 0);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_));
v___x_302_ = 1;
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_);
v___x_304_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_301_, v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15____boxed(lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_));
v___x_309_ = 1;
v___x_310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_);
v___x_311_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_308_, v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17____boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_alloc_closure((void*)(l_String_reduceToList___boxed), 9, 0);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_));
v___x_442_ = 1;
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_);
v___x_444_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_));
v___x_449_ = 1;
v___x_450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_);
v___x_451_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_448_, v___x_449_, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17____boxed(lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
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
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
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
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_alloc_closure((void*)(l_String_reducePush___boxed), 9, 0);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_));
v___x_567_ = 1;
v___x_568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_);
v___x_569_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_566_, v___x_567_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16____boxed(lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_));
v___x_574_ = 1;
v___x_575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_);
v___x_576_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_573_, v___x_574_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18____boxed(lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
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
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
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
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_alloc_closure((void*)(l_String_reduceSingleton___boxed), 9, 0);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_));
v___x_679_ = 1;
v___x_680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_);
v___x_681_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_678_, v___x_679_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15____boxed(lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_));
v___x_686_ = 1;
v___x_687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_);
v___x_688_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_685_, v___x_686_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17____boxed(lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
return v_res_690_;
}
}
static lean_object* _init_l_String_reduceToSingleton___redArg___closed__0(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_box(0);
v___x_692_ = ((lean_object*)(l_String_reduceSingleton___redArg___closed__1));
v___x_693_ = l_Lean_mkConst(v___x_692_, v___x_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToSingleton___redArg(lean_object* v_e_694_){
_start:
{
lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_729_; 
v___x_699_ = l_String_fromExpr_x3f___redArg(v_e_694_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_729_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_729_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_729_;
goto v_resetjp_701_;
}
v___jp_696_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
v_resetjp_701_:
{
if (lean_obj_tag(v_a_700_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_724_; 
v_val_704_ = lean_ctor_get(v_a_700_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_700_);
if (v_isSharedCheck_724_ == 0)
{
v___x_706_ = v_a_700_;
v_isShared_707_ = v_isSharedCheck_724_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_val_704_);
lean_dec(v_a_700_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_724_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_string_data(v_val_704_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_tail_709_; 
v_tail_709_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_tail_709_);
if (lean_obj_tag(v_tail_709_) == 0)
{
lean_object* v_head_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint32_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v_head_710_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_head_710_);
lean_dec_ref(v___x_708_);
v___x_711_ = lean_obj_once(&l_String_reduceToSingleton___redArg___closed__0, &l_String_reduceToSingleton___redArg___closed__0_once, _init_l_String_reduceToSingleton___redArg___closed__0);
v___x_712_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3);
v___x_713_ = lean_unbox_uint32(v_head_710_);
lean_dec(v_head_710_);
v___x_714_ = lean_uint32_to_nat(v___x_713_);
v___x_715_ = l_Lean_mkRawNatLit(v___x_714_);
v___x_716_ = l_Lean_Expr_app___override(v___x_712_, v___x_715_);
v___x_717_ = l_Lean_Expr_app___override(v___x_711_, v___x_716_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 0);
lean_ctor_set(v___x_706_, 0, v___x_717_);
v___x_719_ = v___x_706_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_719_);
v___x_721_ = v___x_702_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_dec_ref(v___x_708_);
lean_dec(v_tail_709_);
lean_del_object(v___x_706_);
lean_del_object(v___x_702_);
goto v___jp_696_;
}
}
else
{
lean_dec(v___x_708_);
lean_del_object(v___x_706_);
lean_del_object(v___x_702_);
goto v___jp_696_;
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_727_; 
lean_dec(v_a_700_);
v___x_725_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_725_);
v___x_727_ = v___x_702_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceToSingleton___redArg___boxed(lean_object* v_e_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_String_reduceToSingleton___redArg(v_e_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToSingleton(lean_object* v_e_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_String_reduceToSingleton___redArg(v_e_733_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_String_reduceToSingleton___boxed(lean_object* v_e_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_String_reduceToSingleton(v_e_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_));
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_));
v___x_764_ = lean_alloc_closure((void*)(l_String_reduceToSingleton___boxed), 9, 0);
v___x_765_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_762_, v___x_763_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12____boxed(lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_();
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg(lean_object* v_declName_770_, lean_object* v_arity_771_, lean_object* v_op_772_, lean_object* v_e_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = l_Lean_Expr_isAppOfArity(v_e_773_, v_declName_770_, v_arity_771_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_e_773_);
lean_dec_ref(v_op_772_);
v___x_780_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_809_; 
v___x_782_ = l_Lean_Expr_appFn_x21(v_e_773_);
v___x_783_ = l_Lean_Expr_appArg_x21(v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_String_fromExpr_x3f___redArg(v___x_783_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_809_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_809_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_809_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_val_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_804_; 
lean_del_object(v___x_787_);
v_val_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_789_);
lean_dec_ref(v_a_785_);
v___x_790_ = l_Lean_Expr_appArg_x21(v_e_773_);
v___x_791_ = l_String_fromExpr_x3f___redArg(v___x_790_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_804_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_804_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_804_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_a_792_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_794_);
v_val_796_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_796_);
lean_dec_ref(v_a_792_);
v___x_797_ = lean_apply_2(v_op_772_, v_val_789_, v_val_796_);
v___x_798_ = lean_unbox(v___x_797_);
v___x_799_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_773_, v___x_798_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec(v_a_792_);
lean_dec(v_val_789_);
lean_dec_ref(v_e_773_);
lean_dec_ref(v_op_772_);
v___x_800_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_800_);
v___x_802_ = v___x_794_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
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
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_a_785_);
lean_dec_ref(v_e_773_);
lean_dec_ref(v_op_772_);
v___x_805_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_805_);
v___x_807_ = v___x_787_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg___boxed(lean_object* v_declName_810_, lean_object* v_arity_811_, lean_object* v_op_812_, lean_object* v_e_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_String_reduceBinPred___redArg(v_declName_810_, v_arity_811_, v_op_812_, v_e_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_declName_810_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred(lean_object* v_declName_820_, lean_object* v_arity_821_, lean_object* v_op_822_, lean_object* v_e_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = l_Lean_Expr_isAppOfArity(v_e_823_, v_declName_820_, v_arity_821_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v_e_823_);
lean_dec_ref(v_op_822_);
v___x_833_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_862_; 
v___x_835_ = l_Lean_Expr_appFn_x21(v_e_823_);
v___x_836_ = l_Lean_Expr_appArg_x21(v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = l_String_fromExpr_x3f___redArg(v___x_836_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_862_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_862_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_862_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
if (lean_obj_tag(v_a_838_) == 1)
{
lean_object* v_val_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_857_; 
lean_del_object(v___x_840_);
v_val_842_ = lean_ctor_get(v_a_838_, 0);
lean_inc(v_val_842_);
lean_dec_ref(v_a_838_);
v___x_843_ = l_Lean_Expr_appArg_x21(v_e_823_);
v___x_844_ = l_String_fromExpr_x3f___redArg(v___x_843_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_857_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_857_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_857_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
if (lean_obj_tag(v_a_845_) == 1)
{
lean_object* v_val_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_847_);
v_val_849_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_val_849_);
lean_dec_ref(v_a_845_);
v___x_850_ = lean_apply_2(v_op_822_, v_val_842_, v_val_849_);
v___x_851_ = lean_unbox(v___x_850_);
v___x_852_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_823_, v___x_851_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_855_; 
lean_dec(v_a_845_);
lean_dec(v_val_842_);
lean_dec_ref(v_e_823_);
lean_dec_ref(v_op_822_);
v___x_853_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_853_);
v___x_855_ = v___x_847_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_a_838_);
lean_dec_ref(v_e_823_);
lean_dec_ref(v_op_822_);
v___x_858_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_858_);
v___x_860_ = v___x_840_;
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
LEAN_EXPORT lean_object* l_String_reduceBinPred___boxed(lean_object* v_declName_863_, lean_object* v_arity_864_, lean_object* v_op_865_, lean_object* v_e_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_String_reduceBinPred(v_declName_863_, v_arity_864_, v_op_865_, v_e_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec(v_declName_863_);
return v_res_875_;
}
}
static lean_object* _init_l_String_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(0);
v___x_882_ = ((lean_object*)(l_String_reduceBoolPred___redArg___closed__2));
v___x_883_ = l_Lean_mkConst(v___x_882_, v___x_881_);
return v___x_883_;
}
}
static lean_object* _init_l_String_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
v___x_889_ = ((lean_object*)(l_String_reduceBoolPred___redArg___closed__5));
v___x_890_ = l_Lean_mkConst(v___x_889_, v___x_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg(lean_object* v_declName_891_, lean_object* v_arity_892_, lean_object* v_op_893_, lean_object* v_e_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = l_Lean_Expr_isAppOfArity(v_e_894_, v_declName_891_, v_arity_892_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v_op_893_);
v___x_897_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_939_; 
v___x_899_ = l_Lean_Expr_appFn_x21(v_e_894_);
v___x_900_ = l_Lean_Expr_appArg_x21(v___x_899_);
lean_dec_ref(v___x_899_);
v___x_901_ = l_String_fromExpr_x3f___redArg(v___x_900_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_939_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_939_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_939_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
if (lean_obj_tag(v_a_902_) == 1)
{
lean_object* v_val_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_934_; 
v_val_906_ = lean_ctor_get(v_a_902_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_902_);
if (v_isSharedCheck_934_ == 0)
{
v___x_908_ = v_a_902_;
v_isShared_909_ = v_isSharedCheck_934_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_val_906_);
lean_dec(v_a_902_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_934_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_933_; 
v___x_910_ = l_Lean_Expr_appArg_x21(v_e_894_);
v___x_911_ = l_String_fromExpr_x3f___redArg(v___x_910_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_933_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_933_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_933_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___y_917_; 
if (lean_obj_tag(v_a_912_) == 1)
{
lean_object* v_val_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
lean_del_object(v___x_904_);
v_val_924_ = lean_ctor_get(v_a_912_, 0);
lean_inc(v_val_924_);
lean_dec_ref(v_a_912_);
v___x_925_ = lean_apply_2(v_op_893_, v_val_906_, v_val_924_);
v___x_926_ = lean_unbox(v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_917_ = v___x_927_;
goto v___jp_916_;
}
else
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_917_ = v___x_928_;
goto v___jp_916_;
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_del_object(v___x_914_);
lean_dec(v_a_912_);
lean_del_object(v___x_908_);
lean_dec(v_val_906_);
lean_dec_ref(v_op_893_);
v___x_929_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_929_);
v___x_931_ = v___x_904_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
v___jp_916_:
{
lean_object* v___x_919_; 
lean_inc_ref(v___y_917_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
lean_ctor_set(v___x_908_, 0, v___y_917_);
v___x_919_ = v___x_908_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___y_917_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_919_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_a_902_);
lean_dec_ref(v_op_893_);
v___x_935_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_935_);
v___x_937_ = v___x_904_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg___boxed(lean_object* v_declName_940_, lean_object* v_arity_941_, lean_object* v_op_942_, lean_object* v_e_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_String_reduceBoolPred___redArg(v_declName_940_, v_arity_941_, v_op_942_, v_e_943_);
lean_dec_ref(v_e_943_);
lean_dec(v_declName_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred(lean_object* v_declName_946_, lean_object* v_arity_947_, lean_object* v_op_948_, lean_object* v_e_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v___x_958_; 
v___x_958_ = l_Lean_Expr_isAppOfArity(v_e_949_, v_declName_946_, v_arity_947_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v_op_948_);
v___x_959_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1001_; 
v___x_961_ = l_Lean_Expr_appFn_x21(v_e_949_);
v___x_962_ = l_Lean_Expr_appArg_x21(v___x_961_);
lean_dec_ref(v___x_961_);
v___x_963_ = l_String_fromExpr_x3f___redArg(v___x_962_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_1001_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1001_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
if (lean_obj_tag(v_a_964_) == 1)
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_996_; 
v_val_968_ = lean_ctor_get(v_a_964_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_996_ == 0)
{
v___x_970_ = v_a_964_;
v_isShared_971_ = v_isSharedCheck_996_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v_a_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_996_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_995_; 
v___x_972_ = l_Lean_Expr_appArg_x21(v_e_949_);
v___x_973_ = l_String_fromExpr_x3f___redArg(v___x_972_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_995_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___y_979_; 
if (lean_obj_tag(v_a_974_) == 1)
{
lean_object* v_val_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
lean_del_object(v___x_966_);
v_val_986_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_val_986_);
lean_dec_ref(v_a_974_);
v___x_987_ = lean_apply_2(v_op_948_, v_val_968_, v_val_986_);
v___x_988_ = lean_unbox(v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_979_ = v___x_989_;
goto v___jp_978_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_979_ = v___x_990_;
goto v___jp_978_;
}
}
else
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_del_object(v___x_976_);
lean_dec(v_a_974_);
lean_del_object(v___x_970_);
lean_dec(v_val_968_);
lean_dec_ref(v_op_948_);
v___x_991_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_991_);
v___x_993_ = v___x_966_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
v___jp_978_:
{
lean_object* v___x_981_; 
lean_inc_ref(v___y_979_);
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 0);
lean_ctor_set(v___x_970_, 0, v___y_979_);
v___x_981_ = v___x_970_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___y_979_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_981_);
v___x_983_ = v___x_976_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v_a_964_);
lean_dec_ref(v_op_948_);
v___x_997_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_997_);
v___x_999_ = v___x_966_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___boxed(lean_object* v_declName_1002_, lean_object* v_arity_1003_, lean_object* v_op_1004_, lean_object* v_e_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_String_reduceBoolPred(v_declName_1002_, v_arity_1003_, v_op_1004_, v_e_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_e_1005_);
lean_dec(v_declName_1002_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___redArg(lean_object* v_e_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = ((lean_object*)(l_String_reduceLT___redArg___closed__2));
v___x_1027_ = lean_unsigned_to_nat(4u);
v___x_1028_ = l_Lean_Expr_isAppOfArity(v_e_1020_, v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_e_1020_);
v___x_1029_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1057_; 
v___x_1031_ = l_Lean_Expr_appFn_x21(v_e_1020_);
v___x_1032_ = l_Lean_Expr_appArg_x21(v___x_1031_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = l_String_fromExpr_x3f___redArg(v___x_1032_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1057_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1057_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
if (lean_obj_tag(v_a_1034_) == 1)
{
lean_object* v_val_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1052_; 
lean_del_object(v___x_1036_);
v_val_1038_ = lean_ctor_get(v_a_1034_, 0);
lean_inc(v_val_1038_);
lean_dec_ref(v_a_1034_);
v___x_1039_ = l_Lean_Expr_appArg_x21(v_e_1020_);
v___x_1040_ = l_String_fromExpr_x3f___redArg(v___x_1039_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
if (lean_obj_tag(v_a_1041_) == 1)
{
lean_object* v_val_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1043_);
v_val_1045_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v_a_1041_);
v___x_1046_ = lean_string_dec_lt(v_val_1038_, v_val_1045_);
lean_dec(v_val_1045_);
lean_dec(v_val_1038_);
v___x_1047_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1020_, v___x_1046_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_dec(v_a_1041_);
lean_dec(v_val_1038_);
lean_dec_ref(v_e_1020_);
v___x_1048_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1048_);
v___x_1050_ = v___x_1043_;
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
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec(v_a_1034_);
lean_dec_ref(v_e_1020_);
v___x_1053_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1053_);
v___x_1055_ = v___x_1036_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___redArg___boxed(lean_object* v_e_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_String_reduceLT___redArg(v_e_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT(lean_object* v_e_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_String_reduceLT___redArg(v_e_1065_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___boxed(lean_object* v_e_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_String_reduceLT(v_e_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1105_ = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
v___x_1106_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1103_, v___x_1104_, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20____boxed(lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
return v_res_1108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1113_ = 1;
v___x_1114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_);
v___x_1115_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1112_, v___x_1113_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22____boxed(lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1120_ = 1;
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_);
v___x_1122_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1119_, v___x_1120_, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24____boxed(lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___redArg(lean_object* v_e_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = ((lean_object*)(l_String_reduceLE___redArg___closed__2));
v___x_1137_ = lean_unsigned_to_nat(4u);
v___x_1138_ = l_Lean_Expr_isAppOfArity(v_e_1130_, v___x_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_e_1130_);
v___x_1139_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1167_; 
v___x_1141_ = l_Lean_Expr_appFn_x21(v_e_1130_);
v___x_1142_ = l_Lean_Expr_appArg_x21(v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = l_String_fromExpr_x3f___redArg(v___x_1142_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1167_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1167_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
if (lean_obj_tag(v_a_1144_) == 1)
{
lean_object* v_val_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1162_; 
lean_del_object(v___x_1146_);
v_val_1148_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_val_1148_);
lean_dec_ref(v_a_1144_);
v___x_1149_ = l_Lean_Expr_appArg_x21(v_e_1130_);
v___x_1150_ = l_String_fromExpr_x3f___redArg(v___x_1149_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
if (lean_obj_tag(v_a_1151_) == 1)
{
lean_object* v_val_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
lean_del_object(v___x_1153_);
v_val_1155_ = lean_ctor_get(v_a_1151_, 0);
lean_inc(v_val_1155_);
lean_dec_ref(v_a_1151_);
v___x_1156_ = l_String_decLE(v_val_1148_, v_val_1155_);
lean_dec(v_val_1155_);
lean_dec(v_val_1148_);
v___x_1157_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1130_, v___x_1156_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_dec(v_a_1151_);
lean_dec(v_val_1148_);
lean_dec_ref(v_e_1130_);
v___x_1158_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1158_);
v___x_1160_ = v___x_1153_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1144_);
lean_dec_ref(v_e_1130_);
v___x_1163_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1163_);
v___x_1165_ = v___x_1146_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___redArg___boxed(lean_object* v_e_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_String_reduceLE___redArg(v_e_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE(lean_object* v_e_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_String_reduceLE___redArg(v_e_1175_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___boxed(lean_object* v_e_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_String_reduceLE(v_e_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1215_ = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
v___x_1216_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1213_, v___x_1214_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20____boxed(lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
return v_res_1218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1223_ = 1;
v___x_1224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_);
v___x_1225_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1222_, v___x_1223_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22____boxed(lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1230_ = 1;
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_);
v___x_1232_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1229_, v___x_1230_, v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24____boxed(lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___redArg(lean_object* v_e_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = ((lean_object*)(l_String_reduceGT___redArg___closed__2));
v___x_1247_ = lean_unsigned_to_nat(4u);
v___x_1248_ = l_Lean_Expr_isAppOfArity(v_e_1240_, v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_e_1240_);
v___x_1249_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1277_; 
v___x_1251_ = l_Lean_Expr_appFn_x21(v_e_1240_);
v___x_1252_ = l_Lean_Expr_appArg_x21(v___x_1251_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = l_String_fromExpr_x3f___redArg(v___x_1252_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1277_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1277_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
if (lean_obj_tag(v_a_1254_) == 1)
{
lean_object* v_val_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
lean_del_object(v___x_1256_);
v_val_1258_ = lean_ctor_get(v_a_1254_, 0);
lean_inc(v_val_1258_);
lean_dec_ref(v_a_1254_);
v___x_1259_ = l_Lean_Expr_appArg_x21(v_e_1240_);
v___x_1260_ = l_String_fromExpr_x3f___redArg(v___x_1259_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_a_1261_) == 1)
{
lean_object* v_val_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
lean_del_object(v___x_1263_);
v_val_1265_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_val_1265_);
lean_dec_ref(v_a_1261_);
v___x_1266_ = lean_string_dec_lt(v_val_1265_, v_val_1258_);
lean_dec(v_val_1258_);
lean_dec(v_val_1265_);
v___x_1267_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1240_, v___x_1266_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec(v_a_1261_);
lean_dec(v_val_1258_);
lean_dec_ref(v_e_1240_);
v___x_1268_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1268_);
v___x_1270_ = v___x_1263_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_dec(v_a_1254_);
lean_dec_ref(v_e_1240_);
v___x_1273_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1273_);
v___x_1275_ = v___x_1256_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___redArg___boxed(lean_object* v_e_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_String_reduceGT___redArg(v_e_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT(lean_object* v_e_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_String_reduceGT___redArg(v_e_1285_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___boxed(lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_String_reduceGT(v_e_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_));
v___x_1311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_));
v___x_1312_ = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
v___x_1313_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1310_, v___x_1311_, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20____boxed(lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
return v_res_1315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_));
v___x_1320_ = 1;
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_);
v___x_1322_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1319_, v___x_1320_, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22____boxed(lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_));
v___x_1327_ = 1;
v___x_1328_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_);
v___x_1329_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1326_, v___x_1327_, v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24____boxed(lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___redArg(lean_object* v_e_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = ((lean_object*)(l_String_reduceGE___redArg___closed__2));
v___x_1344_ = lean_unsigned_to_nat(4u);
v___x_1345_ = l_Lean_Expr_isAppOfArity(v_e_1337_, v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_e_1337_);
v___x_1346_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1374_; 
v___x_1348_ = l_Lean_Expr_appFn_x21(v_e_1337_);
v___x_1349_ = l_Lean_Expr_appArg_x21(v___x_1348_);
lean_dec_ref(v___x_1348_);
v___x_1350_ = l_String_fromExpr_x3f___redArg(v___x_1349_);
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1374_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1374_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
if (lean_obj_tag(v_a_1351_) == 1)
{
lean_object* v_val_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1353_);
v_val_1355_ = lean_ctor_get(v_a_1351_, 0);
lean_inc(v_val_1355_);
lean_dec_ref(v_a_1351_);
v___x_1356_ = l_Lean_Expr_appArg_x21(v_e_1337_);
v___x_1357_ = l_String_fromExpr_x3f___redArg(v___x_1356_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
if (lean_obj_tag(v_a_1358_) == 1)
{
lean_object* v_val_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
lean_del_object(v___x_1360_);
v_val_1362_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v_a_1358_);
v___x_1363_ = l_String_decLE(v_val_1362_, v_val_1355_);
lean_dec(v_val_1355_);
lean_dec(v_val_1362_);
v___x_1364_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1337_, v___x_1363_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec(v_a_1358_);
lean_dec(v_val_1355_);
lean_dec_ref(v_e_1337_);
v___x_1365_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1365_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec(v_a_1351_);
lean_dec_ref(v_e_1337_);
v___x_1370_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1370_);
v___x_1372_ = v___x_1353_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___redArg___boxed(lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_String_reduceGE___redArg(v_e_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE(lean_object* v_e_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_String_reduceGE___redArg(v_e_1382_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___boxed(lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_String_reduceGE(v_e_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_));
v___x_1408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_));
v___x_1409_ = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
v___x_1410_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1407_, v___x_1408_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20____boxed(lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
return v_res_1412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_));
v___x_1417_ = 1;
v___x_1418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_);
v___x_1419_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1416_, v___x_1417_, v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22____boxed(lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_));
v___x_1424_ = 1;
v___x_1425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_);
v___x_1426_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1423_, v___x_1424_, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24____boxed(lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___lam__0(lean_object* v_val_1429_, lean_object* v_val_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Meta_mkStringLitNeProof(v_val_1429_, v_val_1430_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___lam__0___boxed(lean_object* v_val_1440_, lean_object* v_val_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_String_reduceEq___lam__0(v_val_1440_, v_val_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq(lean_object* v_e_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = ((lean_object*)(l_String_reduceEq___closed__1));
v___x_1464_ = lean_unsigned_to_nat(3u);
v___x_1465_ = l_Lean_Expr_isAppOfArity(v_e_1454_, v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_e_1454_);
v___x_1466_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1495_; 
v___x_1468_ = l_Lean_Expr_appFn_x21(v_e_1454_);
v___x_1469_ = l_Lean_Expr_appArg_x21(v___x_1468_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = l_String_fromExpr_x3f___redArg(v___x_1469_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1495_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1495_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_val_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1490_; 
lean_del_object(v___x_1473_);
v_val_1475_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_val_1475_);
lean_dec_ref(v_a_1471_);
v___x_1476_ = l_Lean_Expr_appArg_x21(v_e_1454_);
v___x_1477_ = l_String_fromExpr_x3f___redArg(v___x_1476_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
if (lean_obj_tag(v_a_1478_) == 1)
{
lean_object* v_val_1482_; lean_object* v___f_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
lean_del_object(v___x_1480_);
v_val_1482_ = lean_ctor_get(v_a_1478_, 0);
lean_inc_n(v_val_1482_, 2);
lean_dec_ref(v_a_1478_);
lean_inc(v_val_1475_);
v___f_1483_ = lean_alloc_closure((void*)(l_String_reduceEq___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1483_, 0, v_val_1475_);
lean_closure_set(v___f_1483_, 1, v_val_1482_);
v___x_1484_ = lean_string_dec_eq(v_val_1475_, v_val_1482_);
lean_dec(v_val_1482_);
lean_dec(v_val_1475_);
v___x_1485_ = l_Lean_Meta_Simp_evalEqPropStep(v_e_1454_, v___x_1484_, v___f_1483_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
lean_dec(v_a_1478_);
lean_dec(v_val_1475_);
lean_dec_ref(v_e_1454_);
v___x_1486_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1486_);
v___x_1488_ = v___x_1480_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_dec(v_a_1471_);
lean_dec_ref(v_e_1454_);
v___x_1491_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1491_);
v___x_1493_ = v___x_1473_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
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
}
LEAN_EXPORT lean_object* l_String_reduceEq___boxed(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_String_reduceEq(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_));
v___x_1524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_));
v___x_1525_ = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
v___x_1526_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1523_, v___x_1524_, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20____boxed(lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_();
return v_res_1528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_));
v___x_1533_ = 1;
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_);
v___x_1535_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1532_, v___x_1533_, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22____boxed(lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_();
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_));
v___x_1540_ = 1;
v___x_1541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_);
v___x_1542_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1539_, v___x_1540_, v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24____boxed(lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_();
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe(lean_object* v_e_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1557_ = ((lean_object*)(l_String_reduceNe___closed__1));
v___x_1558_ = lean_unsigned_to_nat(3u);
v___x_1559_ = l_Lean_Expr_isAppOfArity(v_e_1548_, v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref(v_e_1548_);
v___x_1560_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1591_; 
v___x_1562_ = l_Lean_Expr_appFn_x21(v_e_1548_);
v___x_1563_ = l_Lean_Expr_appArg_x21(v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_String_fromExpr_x3f___redArg(v___x_1563_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1591_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1591_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
if (lean_obj_tag(v_a_1565_) == 1)
{
lean_object* v_val_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1586_; 
lean_del_object(v___x_1567_);
v_val_1569_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v_a_1565_);
v___x_1570_ = l_Lean_Expr_appArg_x21(v_e_1548_);
v___x_1571_ = l_String_fromExpr_x3f___redArg(v___x_1570_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1586_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1586_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
if (lean_obj_tag(v_a_1572_) == 1)
{
lean_object* v_val_1576_; lean_object* v___f_1577_; uint8_t v___x_1578_; 
lean_del_object(v___x_1574_);
v_val_1576_ = lean_ctor_get(v_a_1572_, 0);
lean_inc_n(v_val_1576_, 2);
lean_dec_ref(v_a_1572_);
lean_inc(v_val_1569_);
v___f_1577_ = lean_alloc_closure((void*)(l_String_reduceEq___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1577_, 0, v_val_1569_);
lean_closure_set(v___f_1577_, 1, v_val_1576_);
v___x_1578_ = lean_string_dec_eq(v_val_1569_, v_val_1576_);
lean_dec(v_val_1576_);
lean_dec(v_val_1569_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_Simp_evalNePropStep(v_e_1548_, v___x_1559_, v___f_1577_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1579_;
}
else
{
uint8_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = 0;
v___x_1581_ = l_Lean_Meta_Simp_evalNePropStep(v_e_1548_, v___x_1580_, v___f_1577_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1581_;
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_dec(v_a_1572_);
lean_dec(v_val_1569_);
lean_dec_ref(v_e_1548_);
v___x_1582_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1582_);
v___x_1584_ = v___x_1574_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec(v_a_1565_);
lean_dec_ref(v_e_1548_);
v___x_1587_ = ((lean_object*)(l_String_reduceBinPred___redArg___closed__0));
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1587_);
v___x_1589_ = v___x_1567_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___boxed(lean_object* v_e_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_String_reduceNe(v_e_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_));
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_));
v___x_1626_ = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
v___x_1627_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1624_, v___x_1625_, v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20____boxed(lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_();
return v_res_1629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_));
v___x_1634_ = 1;
v___x_1635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_);
v___x_1636_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1633_, v___x_1634_, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22____boxed(lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_();
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_));
v___x_1641_ = 1;
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_);
v___x_1643_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1640_, v___x_1641_, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24____boxed(lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_();
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg(lean_object* v_e_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = ((lean_object*)(l_String_reduceBEq___redArg___closed__2));
v___x_1654_ = lean_unsigned_to_nat(4u);
v___x_1655_ = l_Lean_Expr_isAppOfArity(v_e_1651_, v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1697_; 
v___x_1658_ = l_Lean_Expr_appFn_x21(v_e_1651_);
v___x_1659_ = l_Lean_Expr_appArg_x21(v___x_1658_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = l_String_fromExpr_x3f___redArg(v___x_1659_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1697_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1697_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
if (lean_obj_tag(v_a_1661_) == 1)
{
lean_object* v_val_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1692_; 
v_val_1665_ = lean_ctor_get(v_a_1661_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_a_1661_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1667_ = v_a_1661_;
v_isShared_1668_ = v_isSharedCheck_1692_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_val_1665_);
lean_dec(v_a_1661_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1692_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1691_; 
v___x_1669_ = l_Lean_Expr_appArg_x21(v_e_1651_);
v___x_1670_ = l_String_fromExpr_x3f___redArg(v___x_1669_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1691_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1691_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___y_1676_; 
if (lean_obj_tag(v_a_1671_) == 1)
{
lean_object* v_val_1683_; uint8_t v___x_1684_; 
lean_del_object(v___x_1663_);
v_val_1683_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_val_1683_);
lean_dec_ref(v_a_1671_);
v___x_1684_ = lean_string_dec_eq(v_val_1665_, v_val_1683_);
lean_dec(v_val_1683_);
lean_dec(v_val_1665_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_1676_ = v___x_1685_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_1676_ = v___x_1686_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_del_object(v___x_1673_);
lean_dec(v_a_1671_);
lean_del_object(v___x_1667_);
lean_dec(v_val_1665_);
v___x_1687_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1687_);
v___x_1689_ = v___x_1663_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
v___jp_1675_:
{
lean_object* v___x_1678_; 
lean_inc_ref(v___y_1676_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1676_);
v___x_1678_ = v___x_1667_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___y_1676_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1678_);
v___x_1680_ = v___x_1673_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_dec(v_a_1661_);
v___x_1693_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1693_);
v___x_1695_ = v___x_1663_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
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
}
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg___boxed(lean_object* v_e_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_String_reduceBEq___redArg(v_e_1698_);
lean_dec_ref(v_e_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq(lean_object* v_e_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_String_reduceBEq___redArg(v_e_1701_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___boxed(lean_object* v_e_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_String_reduceBEq(v_e_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_e_1711_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1741_ = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
v___x_1742_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1739_, v___x_1740_, v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20____boxed(lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
return v_res_1744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1749_ = 1;
v___x_1750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_);
v___x_1751_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1748_, v___x_1749_, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22____boxed(lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_));
v___x_1756_ = 1;
v___x_1757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_);
v___x_1758_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1755_, v___x_1756_, v___x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24____boxed(lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg(lean_object* v_e_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = ((lean_object*)(l_String_reduceBNe___redArg___closed__1));
v___x_1767_ = lean_unsigned_to_nat(4u);
v___x_1768_ = l_Lean_Expr_isAppOfArity(v_e_1764_, v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1811_; 
v___x_1771_ = l_Lean_Expr_appFn_x21(v_e_1764_);
v___x_1772_ = l_Lean_Expr_appArg_x21(v___x_1771_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = l_String_fromExpr_x3f___redArg(v___x_1772_);
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1811_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1811_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
if (lean_obj_tag(v_a_1774_) == 1)
{
lean_object* v_val_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1806_; 
v_val_1778_ = lean_ctor_get(v_a_1774_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1774_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1780_ = v_a_1774_;
v_isShared_1781_ = v_isSharedCheck_1806_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_val_1778_);
lean_dec(v_a_1774_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1806_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1805_; 
v___x_1782_ = l_Lean_Expr_appArg_x21(v_e_1764_);
v___x_1783_ = l_String_fromExpr_x3f___redArg(v___x_1782_);
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1805_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1805_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___y_1789_; 
if (lean_obj_tag(v_a_1784_) == 1)
{
lean_object* v_val_1798_; uint8_t v___x_1799_; 
lean_del_object(v___x_1776_);
v_val_1798_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_val_1798_);
lean_dec_ref(v_a_1784_);
v___x_1799_ = lean_string_dec_eq(v_val_1778_, v_val_1798_);
lean_dec(v_val_1798_);
lean_dec(v_val_1778_);
if (v___x_1799_ == 0)
{
if (v___x_1768_ == 0)
{
goto v___jp_1796_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__6, &l_String_reduceBoolPred___redArg___closed__6_once, _init_l_String_reduceBoolPred___redArg___closed__6);
v___y_1789_ = v___x_1800_;
goto v___jp_1788_;
}
}
else
{
goto v___jp_1796_;
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_del_object(v___x_1786_);
lean_dec(v_a_1784_);
lean_del_object(v___x_1780_);
lean_dec(v_val_1778_);
v___x_1801_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1801_);
v___x_1803_ = v___x_1776_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
v___jp_1788_:
{
lean_object* v___x_1791_; 
lean_inc_ref(v___y_1789_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 0);
lean_ctor_set(v___x_1780_, 0, v___y_1789_);
v___x_1791_ = v___x_1780_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___y_1789_);
v___x_1791_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1791_);
v___x_1793_ = v___x_1786_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
v___jp_1796_:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_obj_once(&l_String_reduceBoolPred___redArg___closed__3, &l_String_reduceBoolPred___redArg___closed__3_once, _init_l_String_reduceBoolPred___redArg___closed__3);
v___y_1789_ = v___x_1797_;
goto v___jp_1788_;
}
}
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
lean_dec(v_a_1774_);
v___x_1807_ = ((lean_object*)(l_String_reduceAppend___redArg___closed__3));
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1807_);
v___x_1809_ = v___x_1776_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg___boxed(lean_object* v_e_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_String_reduceBNe___redArg(v_e_1812_);
lean_dec_ref(v_e_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe(lean_object* v_e_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_String_reduceBNe___redArg(v_e_1815_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___boxed(lean_object* v_e_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_String_reduceBNe(v_e_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_e_1825_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1855_ = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
v___x_1856_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1853_, v___x_1854_, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20____boxed(lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
return v_res_1858_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1862_; uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1863_ = 1;
v___x_1864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_);
v___x_1865_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1862_, v___x_1863_, v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22____boxed(lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_));
v___x_1870_ = 1;
v___x_1871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_);
v___x_1872_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1869_, v___x_1870_, v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24____boxed(lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
return v_res_1874_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_StringLitProof(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_StringLitProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
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
lean_object* initialize_Lean_Meta_StringLitProof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_StringLitProof(builtin);
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
