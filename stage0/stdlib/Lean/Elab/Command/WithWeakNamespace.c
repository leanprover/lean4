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
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v_currNamespace_70_; lean_object* v_env_71_; lean_object* v_messages_72_; lean_object* v_scopes_73_; lean_object* v_usedQuotCtxts_74_; lean_object* v_nextMacroScope_75_; lean_object* v_maxRecDepth_76_; lean_object* v_ngen_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_infoState_79_; lean_object* v_traceState_80_; lean_object* v_snapshotTasks_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_139_; 
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
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_139_ == 0)
{
v___x_83_ = v___x_69_;
v_isShared_84_ = v_isSharedCheck_139_;
goto v_resetjp_82_;
}
else
{
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
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_139_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_85_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_resolveNamespaceRelative(v_currNamespace_70_, v_ns_62_);
lean_inc(v___x_85_);
v___x_86_ = l_Lean_Environment_registerNamespace(v_env_71_, v___x_85_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_86_);
v___x_88_ = v___x_83_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_messages_72_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_scopes_73_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_usedQuotCtxts_74_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_nextMacroScope_75_);
lean_ctor_set(v_reuseFailAlloc_138_, 5, v_maxRecDepth_76_);
lean_ctor_set(v_reuseFailAlloc_138_, 6, v_ngen_77_);
lean_ctor_set(v_reuseFailAlloc_138_, 7, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_138_, 8, v_infoState_79_);
lean_ctor_set(v_reuseFailAlloc_138_, 9, v_traceState_80_);
lean_ctor_set(v_reuseFailAlloc_138_, 10, v_snapshotTasks_81_);
v___x_88_ = v_reuseFailAlloc_138_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
v___x_89_ = lean_st_ref_set(v_a_65_, v___x_88_);
v___f_90_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__0), 2, 1);
lean_closure_set(v___f_90_, 0, v___x_85_);
v___x_91_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_90_, v_a_65_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v___f_92_; lean_object* v_r_93_; 
lean_dec_ref(v___x_91_);
v___f_92_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___lam__1), 2, 1);
lean_closure_set(v___f_92_, 0, v_currNamespace_70_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
v_r_93_ = lean_apply_3(v_m_63_, v_a_64_, v_a_65_, lean_box(0));
if (lean_obj_tag(v_r_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; 
v_a_94_ = lean_ctor_get(v_r_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref(v_r_93_);
v___x_95_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_92_, v_a_65_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_95_, 0);
lean_dec(v_unused_103_);
v___x_97_ = v___x_95_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_dec(v___x_95_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v_a_94_);
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_94_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_a_94_);
v_a_104_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_95_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_95_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v_r_93_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v_r_93_);
v___x_113_ = l_Lean_Elab_Command_modifyScope___redArg(v___f_92_, v_a_65_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v___x_113_, 0);
lean_dec(v_unused_121_);
v___x_115_ = v___x_113_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_dec(v___x_113_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 1);
lean_ctor_set(v___x_115_, 0, v_a_112_);
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_112_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_a_112_);
v_a_122_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_113_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_113_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_currNamespace_70_);
lean_dec_ref(v_m_63_);
v_a_130_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_91_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_91_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v_m_63_);
lean_dec(v_ns_62_);
v_a_140_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_67_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_67_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg___boxed(lean_object* v_ns_148_, lean_object* v_m_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v_ns_148_, v_m_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(lean_object* v_00_u03b1_154_, lean_object* v_ns_155_, lean_object* v_m_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v_ns_155_, v_m_156_, v_a_157_, v_a_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___boxed(lean_object* v_00_u03b1_161_, lean_object* v_ns_162_, lean_object* v_m_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace(v_00_u03b1_161_, v_ns_162_, v_m_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg(){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___closed__0);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg___boxed(lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(lean_object* v_00_u03b1_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___boxed(lean_object* v_00_u03b1_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0(v_00_u03b1_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(lean_object* v_x_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4));
lean_inc(v_x_198_);
v___x_203_ = l_Lean_Syntax_isOfKind(v_x_198_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_x_198_);
v___x_204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v_ns_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v_ns_206_ = l_Lean_Syntax_getArg(v_x_198_, v___x_205_);
v___x_207_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__6));
lean_inc(v_ns_206_);
v___x_208_ = l_Lean_Syntax_isOfKind(v_ns_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v_ns_206_);
lean_dec(v_x_198_);
v___x_209_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace_spec__0___redArg();
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_210_ = lean_unsigned_to_nat(2u);
v___x_211_ = l_Lean_Syntax_getArg(v_x_198_, v___x_210_);
lean_dec(v_x_198_);
v___x_212_ = l_Lean_TSyntax_getId(v_ns_206_);
lean_dec(v_ns_206_);
v___x_213_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_213_, 0, v___x_211_);
v___x_214_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_withWeakNamespace___redArg(v___x_212_, v___x_213_, v_a_199_, v_a_200_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed(lean_object* v_x_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace(v_x_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1(){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___closed__4));
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___closed__13));
v___x_258_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___boxed), 4, 0);
v___x_259_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_255_, v___x_256_, v___x_257_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1___boxed(lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace___regBuiltin___private_Lean_Elab_Command_WithWeakNamespace_0__Lean_Elab_Command_elabWithWeakNamespace__1();
return v_res_261_;
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
