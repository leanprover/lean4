// Lean compiler output
// Module: Lean.Elab.Tactic.Epr
// Imports: import Lean.Meta.Tactic.Epr import Init.Tactics import Lean.Elab.Tactic.BVDecide import Lean.Meta.Tactic.BVDecide.Attr
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabEprConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_epr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "epr"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(67, 110, 239, 224, 62, 183, 238, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Epr"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(56, 126, 167, 84, 133, 50, 202, 232)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(177, 188, 79, 67, 253, 148, 110, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 143, 112, 94, 33, 219, 195, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 239, 39, 174, 244, 67, 99, 222)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 14, 144, 211, 5, 13, 149, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 82, 157, 222, 94, 251, 177, 54)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalEpr"};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(96, 197, 70, 117, 239, 71, 47, 171)}};
static const lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0(lean_object* v_snd_31_, lean_object* v_ref_32_, lean_object* v_a_x3f_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_io_remove_file(v_snd_31_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec(v_ref_32_);
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_55_; 
v_a_44_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_55_ == 0)
{
v___x_46_ = v___x_35_;
v_isShared_47_ = v_isSharedCheck_55_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_35_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_55_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_48_ = lean_io_error_to_string(v_a_44_);
v___x_49_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
v___x_50_ = l_Lean_MessageData_ofFormat(v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v_ref_32_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_51_);
v___x_53_ = v___x_46_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0___boxed(lean_object* v_snd_56_, lean_object* v_ref_57_, lean_object* v_a_x3f_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0(v_snd_56_, v_ref_57_, v_a_x3f_58_);
lean_dec(v_a_x3f_58_);
lean_dec_ref(v_snd_56_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg(lean_object* v_f_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_ref_71_; lean_object* v___x_72_; 
v_ref_71_ = lean_ctor_get(v___y_68_, 2);
v___x_72_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_fst_74_; lean_object* v_snd_75_; lean_object* v_r_76_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v_fst_74_ = lean_ctor_get(v_a_73_, 0);
lean_inc(v_fst_74_);
v_snd_75_ = lean_ctor_get(v_a_73_, 1);
lean_inc_n(v_snd_75_, 2);
lean_dec(v_a_73_);
lean_inc(v___y_69_);
lean_inc_ref(v___y_68_);
lean_inc(v___y_67_);
lean_inc_ref(v___y_66_);
lean_inc(v___y_65_);
lean_inc_ref(v___y_64_);
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
v_r_76_ = lean_apply_11(v_f_61_, v_fst_74_, v_snd_75_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, lean_box(0));
if (lean_obj_tag(v_r_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_101_; 
v_a_77_ = lean_ctor_get(v_r_76_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_r_76_);
if (v_isSharedCheck_101_ == 0)
{
v___x_79_ = v_r_76_;
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v_r_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
lean_inc(v_a_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 1);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_100_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; 
lean_inc(v_ref_71_);
v___x_83_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0(v_snd_75_, v_ref_71_, v___x_82_);
lean_dec_ref(v___x_82_);
lean_dec(v_snd_75_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_91_);
v___x_85_ = v___x_83_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_dec(v___x_83_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v_a_77_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_77_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v_a_77_);
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_102_ = lean_ctor_get(v_r_76_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v_r_76_, 1);
v___x_103_ = lean_box(0);
lean_inc(v_ref_71_);
v___x_104_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___lam__0(v_snd_75_, v_ref_71_, v___x_103_);
lean_dec(v_snd_75_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___x_104_, 0);
lean_dec(v_unused_112_);
v___x_106_ = v___x_104_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_dec(v___x_104_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set_tag(v___x_106_, 1);
lean_ctor_set(v___x_106_, 0, v_a_102_);
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_102_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_a_102_);
v_a_113_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_104_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_104_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_f_61_);
v_a_121_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v___x_72_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_72_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_125_ = lean_io_error_to_string(v_a_121_);
v___x_126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___x_127_ = l_Lean_MessageData_ofFormat(v___x_126_);
lean_inc(v_ref_71_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_ref_71_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_128_);
v___x_130_ = v___x_123_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg___boxed(lean_object* v_f_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg(v_f_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1(lean_object* v_00_u03b1_144_, lean_object* v_f_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg(v_f_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___boxed(lean_object* v_00_u03b1_156_, lean_object* v_f_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1(v_00_u03b1_156_, v_f_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__0(lean_object* v_a_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_170_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = l_Lean_Meta_Tactic_epr(v_a_179_, v_a_168_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref_known(v___x_180_, 1);
v___x_181_ = lean_box(0);
v___x_182_ = lean_box(0);
v___x_183_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_181_, v___y_170_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_191_);
v___x_185_ = v___x_183_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_dec(v___x_183_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_182_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_182_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
return v___x_183_;
}
}
else
{
return v___x_180_;
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_a_168_);
v_a_192_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_178_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_178_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__0___boxed(lean_object* v_a_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__0(v_a_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1(lean_object* v_a_215_, lean_object* v_x_216_, lean_object* v_lratFile_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___closed__1));
v___x_228_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_217_, v_a_215_, v___x_227_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___f_230_; lean_object* v___x_231_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v___f_230_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__0___boxed), 10, 1);
lean_closure_set(v___f_230_, 0, v_a_229_);
v___x_231_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_230_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
return v___x_231_;
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_228_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_228_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___boxed(lean_object* v_a_240_, lean_object* v_x_241_, lean_object* v_lratFile_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1(v_a_240_, v_x_241_, v_lratFile_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v_x_241_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr(lean_object* v_x_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4));
lean_inc(v_x_268_);
v___x_279_ = l_Lean_Syntax_isOfKind(v_x_268_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec(v_x_268_);
v___x_280_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg();
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = l_Lean_Syntax_getArg(v_x_268_, v___x_281_);
lean_dec(v_x_268_);
v___x_283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__6));
lean_inc(v___x_282_);
v___x_284_ = l_Lean_Syntax_isOfKind(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
lean_dec(v___x_282_);
v___x_285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__0___redArg();
return v___x_285_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref_known(v___x_286_, 1);
v___x_287_ = lean_unsigned_to_nat(10u);
v___x_288_ = 0;
v___x_289_ = lean_unsigned_to_nat(100000u);
v___x_290_ = 0;
v___x_291_ = lean_unsigned_to_nat(1000u);
v___x_292_ = 1;
v___x_293_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v___x_293_, 0, v___x_287_);
lean_ctor_set(v___x_293_, 1, v___x_289_);
lean_ctor_set(v___x_293_, 2, v___x_291_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3, v___x_284_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 1, v___x_284_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 2, v___x_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 3, v___x_284_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 4, v___x_284_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 5, v___x_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 6, v___x_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 7, v___x_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 8, v___x_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 9, v___x_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 10, v___x_290_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 11, v___x_284_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 12, v___x_284_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 13, v___x_292_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 14, v___x_284_);
v___x_294_ = l_Lean_Meta_Tactic_BVDecide_elabEprConfig___redArg(v___x_282_, v___x_293_, v___x_284_, v_a_269_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___f_296_; lean_object* v___x_297_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___f_296_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___lam__1___boxed), 12, 1);
lean_closure_set(v___f_296_, 0, v_a_295_);
v___x_297_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr_spec__1___redArg(v___f_296_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_297_;
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v_a_298_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_294_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_dec(v___x_282_);
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___boxed(lean_object* v_x_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr(v_x_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1(){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___closed__4));
v___x_357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___closed__14));
v___x_358_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___boxed), 10, 0);
v___x_359_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_355_, v___x_356_, v___x_357_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1___boxed(lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1();
return v_res_361_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Epr(uint8_t builtin);
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Epr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr___regBuiltin___private_Lean_Elab_Tactic_Epr_0__Lean_Elab_Tactic_Epr_evalEpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Epr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Epr(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Epr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Epr(builtin);
}
#ifdef __cplusplus
}
#endif
