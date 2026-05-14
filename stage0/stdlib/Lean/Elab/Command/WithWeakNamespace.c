// Lean compiler output
// Module: Lean.Elab.Command.WithWeakNamespace
// Imports: public import Lean.Elab.Command
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
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withWeakNamespace"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(9, 218, 49, 83, 69, 150, 121, 239)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(213, 110, 145, 192, 78, 206, 42, 5)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "WithWeakNamespace"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(178, 204, 116, 111, 109, 149, 139, 140)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(179, 30, 198, 36, 76, 129, 46, 14)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 108, 236, 79, 190, 22, 42, 114)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 33, 229, 39, 87, 9, 137, 83)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 205, 64, 83, 73, 22, 55, 78)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabWithWeakNamespace"};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(254, 104, 7, 206, 3, 89, 185, 141)}};
static const lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(lean_object* v_ns_2_, lean_object* v_x_3_){
_start:
{
switch(lean_obj_tag(v_x_3_))
{
case 0:
{
lean_inc(v_ns_2_);
return v_ns_2_;
}
case 1:
{
lean_object* v_pre_4_; lean_object* v_str_5_; 
v_pre_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_pre_4_);
v_str_5_ = lean_ctor_get(v_x_3_, 1);
lean_inc_ref(v_str_5_);
lean_dec_ref(v_x_3_);
if (lean_obj_tag(v_pre_4_) == 0)
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___closed__0));
v___x_10_ = lean_string_dec_eq(v_str_5_, v___x_9_);
if (v___x_10_ == 0)
{
goto v___jp_6_;
}
else
{
lean_dec_ref(v_str_5_);
return v_pre_4_;
}
}
else
{
goto v___jp_6_;
}
v___jp_6_:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_ns_2_, v_pre_4_);
v___x_8_ = l_Lean_Name_str___override(v___x_7_, v_str_5_);
return v___x_8_;
}
}
default: 
{
lean_object* v_pre_11_; lean_object* v_i_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_pre_11_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_pre_11_);
v_i_12_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_i_12_);
lean_dec_ref(v_x_3_);
v___x_13_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_ns_2_, v_pre_11_);
v___x_14_ = l_Lean_Name_num___override(v___x_13_, v_i_12_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative___boxed(lean_object* v_ns_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_ns_15_, v_x_16_);
lean_dec(v_ns_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__0(lean_object* v___x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_header_20_; lean_object* v_opts_21_; lean_object* v_openDecls_22_; lean_object* v_levelNames_23_; lean_object* v_varDecls_24_; lean_object* v_varUIds_25_; lean_object* v_includedVars_26_; lean_object* v_omittedVars_27_; uint8_t v_isNoncomputable_28_; uint8_t v_isPublic_29_; uint8_t v_isMeta_30_; lean_object* v_attrs_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_header_20_ = lean_ctor_get(v_x_19_, 0);
v_opts_21_ = lean_ctor_get(v_x_19_, 1);
v_openDecls_22_ = lean_ctor_get(v_x_19_, 3);
v_levelNames_23_ = lean_ctor_get(v_x_19_, 4);
v_varDecls_24_ = lean_ctor_get(v_x_19_, 5);
v_varUIds_25_ = lean_ctor_get(v_x_19_, 6);
v_includedVars_26_ = lean_ctor_get(v_x_19_, 7);
v_omittedVars_27_ = lean_ctor_get(v_x_19_, 8);
v_isNoncomputable_28_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*10);
v_isPublic_29_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*10 + 1);
v_isMeta_30_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*10 + 2);
v_attrs_31_ = lean_ctor_get(v_x_19_, 9);
v_isSharedCheck_38_ = !lean_is_exclusive(v_x_19_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; 
v_unused_39_ = lean_ctor_get(v_x_19_, 2);
lean_dec(v_unused_39_);
v___x_33_ = v_x_19_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_attrs_31_);
lean_inc(v_omittedVars_27_);
lean_inc(v_includedVars_26_);
lean_inc(v_varUIds_25_);
lean_inc(v_varDecls_24_);
lean_inc(v_levelNames_23_);
lean_inc(v_openDecls_22_);
lean_inc(v_opts_21_);
lean_inc(v_header_20_);
lean_dec(v_x_19_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 2, v___x_18_);
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_header_20_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_opts_21_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_openDecls_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_levelNames_23_);
lean_ctor_set(v_reuseFailAlloc_37_, 5, v_varDecls_24_);
lean_ctor_set(v_reuseFailAlloc_37_, 6, v_varUIds_25_);
lean_ctor_set(v_reuseFailAlloc_37_, 7, v_includedVars_26_);
lean_ctor_set(v_reuseFailAlloc_37_, 8, v_omittedVars_27_);
lean_ctor_set(v_reuseFailAlloc_37_, 9, v_attrs_31_);
lean_ctor_set_uint8(v_reuseFailAlloc_37_, sizeof(void*)*10, v_isNoncomputable_28_);
lean_ctor_set_uint8(v_reuseFailAlloc_37_, sizeof(void*)*10 + 1, v_isPublic_29_);
lean_ctor_set_uint8(v_reuseFailAlloc_37_, sizeof(void*)*10 + 2, v_isMeta_30_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__1(lean_object* v_currNamespace_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_header_42_; lean_object* v_opts_43_; lean_object* v_openDecls_44_; lean_object* v_levelNames_45_; lean_object* v_varDecls_46_; lean_object* v_varUIds_47_; lean_object* v_includedVars_48_; lean_object* v_omittedVars_49_; uint8_t v_isNoncomputable_50_; uint8_t v_isPublic_51_; uint8_t v_isMeta_52_; lean_object* v_attrs_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_header_42_ = lean_ctor_get(v_x_41_, 0);
v_opts_43_ = lean_ctor_get(v_x_41_, 1);
v_openDecls_44_ = lean_ctor_get(v_x_41_, 3);
v_levelNames_45_ = lean_ctor_get(v_x_41_, 4);
v_varDecls_46_ = lean_ctor_get(v_x_41_, 5);
v_varUIds_47_ = lean_ctor_get(v_x_41_, 6);
v_includedVars_48_ = lean_ctor_get(v_x_41_, 7);
v_omittedVars_49_ = lean_ctor_get(v_x_41_, 8);
v_isNoncomputable_50_ = lean_ctor_get_uint8(v_x_41_, sizeof(void*)*10);
v_isPublic_51_ = lean_ctor_get_uint8(v_x_41_, sizeof(void*)*10 + 1);
v_isMeta_52_ = lean_ctor_get_uint8(v_x_41_, sizeof(void*)*10 + 2);
v_attrs_53_ = lean_ctor_get(v_x_41_, 9);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v_x_41_, 2);
lean_dec(v_unused_61_);
v___x_55_ = v_x_41_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_attrs_53_);
lean_inc(v_omittedVars_49_);
lean_inc(v_includedVars_48_);
lean_inc(v_varUIds_47_);
lean_inc(v_varDecls_46_);
lean_inc(v_levelNames_45_);
lean_inc(v_openDecls_44_);
lean_inc(v_opts_43_);
lean_inc(v_header_42_);
lean_dec(v_x_41_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 2, v_currNamespace_40_);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_header_42_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_opts_43_);
lean_ctor_set(v_reuseFailAlloc_59_, 2, v_currNamespace_40_);
lean_ctor_set(v_reuseFailAlloc_59_, 3, v_openDecls_44_);
lean_ctor_set(v_reuseFailAlloc_59_, 4, v_levelNames_45_);
lean_ctor_set(v_reuseFailAlloc_59_, 5, v_varDecls_46_);
lean_ctor_set(v_reuseFailAlloc_59_, 6, v_varUIds_47_);
lean_ctor_set(v_reuseFailAlloc_59_, 7, v_includedVars_48_);
lean_ctor_set(v_reuseFailAlloc_59_, 8, v_omittedVars_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 9, v_attrs_53_);
lean_ctor_set_uint8(v_reuseFailAlloc_59_, sizeof(void*)*10, v_isNoncomputable_50_);
lean_ctor_set_uint8(v_reuseFailAlloc_59_, sizeof(void*)*10 + 1, v_isPublic_51_);
lean_ctor_set_uint8(v_reuseFailAlloc_59_, sizeof(void*)*10 + 2, v_isMeta_52_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(lean_object* v_ns_62_, lean_object* v_m_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_Command_getScope___redArg(v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v_currNamespace_70_; lean_object* v_env_71_; lean_object* v_messages_72_; lean_object* v_scopes_73_; lean_object* v_usedQuotCtxts_74_; lean_object* v_nextMacroScope_75_; lean_object* v_maxRecDepth_76_; lean_object* v_ngen_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_infoState_79_; lean_object* v_traceState_80_; lean_object* v_snapshotTasks_81_; lean_object* v_newDecls_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_140_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v___x_67_);
v___x_69_ = lean_st_ref_take(v_a_65_);
v_currNamespace_70_ = lean_ctor_get(v_a_68_, 2);
lean_inc(v_currNamespace_70_);
lean_dec(v_a_68_);
v_env_71_ = lean_ctor_get(v___x_69_, 0);
v_messages_72_ = lean_ctor_get(v___x_69_, 1);
v_scopes_73_ = lean_ctor_get(v___x_69_, 2);
v_usedQuotCtxts_74_ = lean_ctor_get(v___x_69_, 3);
v_nextMacroScope_75_ = lean_ctor_get(v___x_69_, 4);
v_maxRecDepth_76_ = lean_ctor_get(v___x_69_, 5);
v_ngen_77_ = lean_ctor_get(v___x_69_, 6);
v_auxDeclNGen_78_ = lean_ctor_get(v___x_69_, 7);
v_infoState_79_ = lean_ctor_get(v___x_69_, 8);
v_traceState_80_ = lean_ctor_get(v___x_69_, 9);
v_snapshotTasks_81_ = lean_ctor_get(v___x_69_, 10);
v_newDecls_82_ = lean_ctor_get(v___x_69_, 11);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_140_ == 0)
{
v___x_84_ = v___x_69_;
v_isShared_85_ = v_isSharedCheck_140_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_newDecls_82_);
lean_inc(v_snapshotTasks_81_);
lean_inc(v_traceState_80_);
lean_inc(v_infoState_79_);
lean_inc(v_auxDeclNGen_78_);
lean_inc(v_ngen_77_);
lean_inc(v_maxRecDepth_76_);
lean_inc(v_nextMacroScope_75_);
lean_inc(v_usedQuotCtxts_74_);
lean_inc(v_scopes_73_);
lean_inc(v_messages_72_);
lean_inc(v_env_71_);
lean_dec(v___x_69_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_140_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_86_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_currNamespace_70_, v_ns_62_);
lean_inc(v___x_86_);
v___x_87_ = l_Lean_Environment_registerNamespace(v_env_71_, v___x_86_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_87_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_messages_72_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_scopes_73_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_usedQuotCtxts_74_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v_nextMacroScope_75_);
lean_ctor_set(v_reuseFailAlloc_139_, 5, v_maxRecDepth_76_);
lean_ctor_set(v_reuseFailAlloc_139_, 6, v_ngen_77_);
lean_ctor_set(v_reuseFailAlloc_139_, 7, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_139_, 8, v_infoState_79_);
lean_ctor_set(v_reuseFailAlloc_139_, 9, v_traceState_80_);
lean_ctor_set(v_reuseFailAlloc_139_, 10, v_snapshotTasks_81_);
lean_ctor_set(v_reuseFailAlloc_139_, 11, v_newDecls_82_);
v___x_89_ = v_reuseFailAlloc_139_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v___x_90_ = lean_st_ref_set(v_a_65_, v___x_89_);
v___f_91_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__0), 2, 1);
lean_closure_set(v___f_91_, 0, v___x_86_);
v___x_92_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_91_, v_a_65_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___f_93_; lean_object* v_r_94_; 
lean_dec_ref(v___x_92_);
v___f_93_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__1), 2, 1);
lean_closure_set(v___f_93_, 0, v_currNamespace_70_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
v_r_94_ = lean_apply_3(v_m_63_, v_a_64_, v_a_65_, lean_box(0));
if (lean_obj_tag(v_r_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; 
v_a_95_ = lean_ctor_get(v_r_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref(v_r_94_);
v___x_96_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_93_, v_a_65_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v___x_96_, 0);
lean_dec(v_unused_104_);
v___x_98_ = v___x_96_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_dec(v___x_96_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v_a_95_);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_95_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec(v_a_95_);
v_a_105_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_96_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_96_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_114_; 
v_a_113_ = lean_ctor_get(v_r_94_, 0);
lean_inc(v_a_113_);
lean_dec_ref(v_r_94_);
v___x_114_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_93_, v_a_65_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_121_ == 0)
{
lean_object* v_unused_122_; 
v_unused_122_ = lean_ctor_get(v___x_114_, 0);
lean_dec(v_unused_122_);
v___x_116_ = v___x_114_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_dec(v___x_114_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
lean_ctor_set(v___x_116_, 0, v_a_113_);
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_113_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_113_);
v_a_123_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_114_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_114_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_currNamespace_70_);
lean_dec_ref(v_m_63_);
v_a_131_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_92_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_92_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v_m_63_);
lean_dec(v_ns_62_);
v_a_141_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_67_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_67_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___boxed(lean_object* v_ns_149_, lean_object* v_m_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v_ns_149_, v_m_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(lean_object* v_00_u03b1_155_, lean_object* v_ns_156_, lean_object* v_m_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v_ns_156_, v_m_157_, v_a_158_, v_a_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___boxed(lean_object* v_00_u03b1_162_, lean_object* v_ns_163_, lean_object* v_m_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(v_00_u03b1_162_, v_ns_163_, v_m_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
v___x_170_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg(){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___boxed(lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(lean_object* v_00_u03b1_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___boxed(lean_object* v_00_u03b1_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(v_00_u03b1_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4));
lean_inc(v_x_199_);
v___x_204_ = l_Lean_Syntax_isOfKind(v_x_199_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_x_199_);
v___x_205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v_ns_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v_ns_207_ = l_Lean_Syntax_getArg(v_x_199_, v___x_206_);
v___x_208_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6));
lean_inc(v_ns_207_);
v___x_209_ = l_Lean_Syntax_isOfKind(v_ns_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec(v_ns_207_);
lean_dec(v_x_199_);
v___x_210_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_211_ = lean_unsigned_to_nat(2u);
v___x_212_ = l_Lean_Syntax_getArg(v_x_199_, v___x_211_);
lean_dec(v_x_199_);
v___x_213_ = l_Lean_TSyntax_getId(v_ns_207_);
lean_dec(v_ns_207_);
v___x_214_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_214_, 0, v___x_212_);
v___x_215_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v___x_213_, v___x_214_, v_a_200_, v_a_201_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(v_x_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1(){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_256_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4));
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13));
v___x_259_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed), 4, 0);
v___x_260_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_256_, v___x_257_, v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___boxed(lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1();
return v_res_262_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Command_WithWeakNamespace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Command_WithWeakNamespace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Command_WithWeakNamespace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
}
#ifdef __cplusplus
}
#endif
