// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Misc
// Imports: public import Lean.Elab.Do.Basic public import Lean.Elab.BuiltinDo.Forward meta import Lean.Parser.Do
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
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoSkip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_elabDoSkip___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoSkip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_elabDoSkip___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoSkip___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_elabDoSkip___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoSkip___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_elabDoSkip___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoSkip___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_elabDoSkip___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoSkip___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_elabDoSkip___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoSkip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoSkip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoSkip"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 10, 110, 145, 7, 15, 250, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_elabDoExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoExpr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_elabDoExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 200, 228, 172, 227, 32, 11, 22)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoNested___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_elabDoNested___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoNested___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoNested___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoNested___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_elabDoNested___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoNested___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoNested(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoNested___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoNested"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 1, 47, 68, 131, 32, 43, 94)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__5_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoUnless___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoUnless___closed__9;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__11_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoUnless___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__13_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_elabDoUnless___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Elab_Do_elabDoUnless___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoUnless___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoUnless(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoUnless___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoUnless"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 150, 43, 228, 51, 25, 139, 111)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dbgTrace"};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dbg_trace"};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoDbgTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoDbgTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dbg_trace body"};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoDbgTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__2_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoDbgTrace___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoDbgTrace___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoDbgTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoDbgTrace___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoDbgTrace"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 164, 10, 186, 155, 223, 105, 130)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "assert!"};
static const lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoAssert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_elabDoAssert___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoAssert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_elabDoAssert___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoAssert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "assert! body"};
static const lean_object* l_Lean_Elab_Do_elabDoAssert___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoAssert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__2_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoAssert___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoAssert___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoAssert___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoAssert___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoAssert"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 163, 6, 149, 129, 216, 204, 171)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "debugAssert"};
static const lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "debug_assert!"};
static const lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoDebugAssert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_elabDoDebugAssert___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_elabDoDebugAssert___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoDebugAssert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "debug_assert! body"};
static const lean_object* l_Lean_Elab_Do_elabDoDebugAssert___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoDebugAssert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__2_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoDebugAssert___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoDebugAssert___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoDebugAssert___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoDebugAssert___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "elabDoDebugAssert"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 134, 27, 234, 76, 75, 178, 233)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0(void){
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___boxed(lean_object* v_00_u03b1_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(v_00_u03b1_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_30_;
}
}
lean_object* l_Lean_Elab_Do_elabDoSkip(lean_object* v_stx_42_, lean_object* v_dec_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__5));
lean_inc(v_stx_42_);
v___x_53_ = l_Lean_Syntax_isOfKind(v_stx_42_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec_ref(v_dec_43_);
lean_dec(v_stx_42_);
v___x_54_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v_tk_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v_tk_56_ = l_Lean_Syntax_getArg(v_stx_42_, v___x_55_);
lean_dec(v_stx_42_);
v___x_57_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_43_, v_tk_56_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_tk_56_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_57_, 1);
v___x_59_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_58_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
return v___x_59_;
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_57_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_57_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
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
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoSkip_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_42_ = stack[0].m_obj;
lean_object* v_dec_43_ = stack[1].m_obj;
lean_object* v_a_44_ = stack[2].m_obj;
lean_object* v_a_45_ = stack[3].m_obj;
lean_object* v_a_46_ = stack[4].m_obj;
lean_object* v_a_47_ = stack[5].m_obj;
lean_object* v_a_48_ = stack[6].m_obj;
lean_object* v_a_49_ = stack[7].m_obj;
lean_object* v_a_50_ = stack[8].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_Elab_Do_elabDoSkip(v_stx_42_, v_dec_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoSkip___boxed(lean_object* v_stx_69_, lean_object* v_dec_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Elab_Do_elabDoSkip(v_stx_69_, v_dec_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_79_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1(){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_89_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_90_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__5));
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3));
v___x_92_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSkip___boxed), 10, 0);
v___x_93_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_89_, v___x_90_, v___x_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_94_;
v_res_94_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___boxed(lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
return v_res_96_;
}
}
lean_object* l_Lean_Elab_Do_elabDoExpr(lean_object* v_stx_103_, lean_object* v_dec_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Do_elabDoExpr___closed__1));
lean_inc(v_stx_103_);
v___x_114_ = l_Lean_Syntax_isOfKind(v_stx_103_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec_ref(v_dec_104_);
lean_dec(v_stx_103_);
v___x_115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v_e_117_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v_e_117_ = l_Lean_Syntax_getArg(v_stx_103_, v___x_116_);
lean_dec(v_stx_103_);
lean_inc_ref(v_dec_104_);
lean_inc(v_e_117_);
v___x_118_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_117_, v_dec_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_141_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_141_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_141_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_141_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
if (lean_obj_tag(v_a_119_) == 1)
{
lean_object* v_val_123_; lean_object* v___x_125_; 
lean_dec(v_e_117_);
lean_dec_ref(v_dec_104_);
v_val_123_ = lean_ctor_get(v_a_119_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_a_119_, 1);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_val_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_val_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v_resultType_127_; lean_object* v___x_128_; 
lean_del_object(v___x_121_);
lean_dec(v_a_119_);
v_resultType_127_ = lean_ctor_get(v_dec_104_, 1);
lean_inc_ref(v_resultType_127_);
v___x_128_ = l_Lean_Elab_Do_mkMonadApp(v_resultType_127_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_140_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_140_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_140_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_140_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_139_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = l_Lean_Elab_Term_elabTermEnsuringType(v_e_117_, v___x_134_, v___x_114_, v___x_114_, v___x_135_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_dec_104_, v_a_137_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
return v___x_138_;
}
else
{
lean_dec_ref(v_dec_104_);
return v___x_136_;
}
}
}
}
else
{
lean_dec(v_e_117_);
lean_dec_ref(v_dec_104_);
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_e_117_);
lean_dec_ref(v_dec_104_);
v_a_142_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_118_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_118_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_103_ = stack[0].m_obj;
lean_object* v_dec_104_ = stack[1].m_obj;
lean_object* v_a_105_ = stack[2].m_obj;
lean_object* v_a_106_ = stack[3].m_obj;
lean_object* v_a_107_ = stack[4].m_obj;
lean_object* v_a_108_ = stack[5].m_obj;
lean_object* v_a_109_ = stack[6].m_obj;
lean_object* v_a_110_ = stack[7].m_obj;
lean_object* v_a_111_ = stack[8].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_Elab_Do_elabDoExpr(v_stx_103_, v_dec_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoExpr___boxed(lean_object* v_stx_151_, lean_object* v_dec_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_Do_elabDoExpr(v_stx_151_, v_dec_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_161_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1(){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_169_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_170_ = ((lean_object*)(l_Lean_Elab_Do_elabDoExpr___closed__1));
v___x_171_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1));
v___x_172_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoExpr___boxed), 10, 0);
v___x_173_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_169_, v___x_170_, v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_174_;
v_res_174_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
return v_res_176_;
}
}
lean_object* l_Lean_Elab_Do_elabDoNested(lean_object* v_stx_183_, lean_object* v_dec_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_Do_elabDoNested___closed__1));
lean_inc(v_stx_183_);
v___x_194_ = l_Lean_Syntax_isOfKind(v_stx_183_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec_ref(v_dec_184_);
lean_dec(v_stx_183_);
v___x_195_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = l_Lean_Syntax_getArg(v_stx_183_, v___x_196_);
lean_dec(v_stx_183_);
v___x_198_ = l_Lean_Elab_Do_elabDoSeq(v___x_197_, v_dec_184_, v___x_194_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_198_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoNested_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_183_ = stack[0].m_obj;
lean_object* v_dec_184_ = stack[1].m_obj;
lean_object* v_a_185_ = stack[2].m_obj;
lean_object* v_a_186_ = stack[3].m_obj;
lean_object* v_a_187_ = stack[4].m_obj;
lean_object* v_a_188_ = stack[5].m_obj;
lean_object* v_a_189_ = stack[6].m_obj;
lean_object* v_a_190_ = stack[7].m_obj;
lean_object* v_a_191_ = stack[8].m_obj;
lean_object* v_res_199_;
v_res_199_ = l_Lean_Elab_Do_elabDoNested(v_stx_183_, v_dec_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoNested___boxed(lean_object* v_stx_200_, lean_object* v_dec_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_Do_elabDoNested(v_stx_200_, v_dec_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec_ref(v_a_202_);
return v_res_210_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1(){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_218_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_219_ = ((lean_object*)(l_Lean_Elab_Do_elabDoNested___closed__1));
v___x_220_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1));
v___x_221_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoNested___boxed), 10, 0);
v___x_222_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_218_, v___x_219_, v___x_220_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_223_;
v_res_223_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___boxed(lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
return v_res_225_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoUnless___closed__9(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Array_mkArray0___redArg();
return v___x_248_;
}
}
lean_object* l_Lean_Elab_Do_elabDoUnless(lean_object* v_stx_264_, lean_object* v_dec_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__1));
lean_inc(v_stx_264_);
v___x_275_ = l_Lean_Syntax_isOfKind(v_stx_264_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v_dec_265_);
lean_dec(v_stx_264_);
v___x_276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_276_;
}
else
{
lean_object* v_ref_277_; lean_object* v___x_278_; lean_object* v_tk_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_ref_277_ = lean_ctor_get(v_a_271_, 2);
v___x_278_ = lean_unsigned_to_nat(0u);
v_tk_279_ = l_Lean_Syntax_getArg(v_stx_264_, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = l_Lean_Syntax_getArg(v_stx_264_, v___x_280_);
v___x_282_ = lean_unsigned_to_nat(3u);
v___x_283_ = l_Lean_Syntax_getArg(v_stx_264_, v___x_282_);
lean_dec(v_stx_264_);
v___x_284_ = 0;
v___x_285_ = l_Lean_SourceInfo_fromRef(v_ref_277_, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__3));
v___x_287_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__4));
lean_inc_n(v___x_285_, 10);
v___x_288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__6));
v___x_290_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__8));
v___x_291_ = lean_obj_once(&l_Lean_Elab_Do_elabDoUnless___closed__9, &l_Lean_Elab_Do_elabDoUnless___closed__9_once, _init_l_Lean_Elab_Do_elabDoUnless___closed__9);
v___x_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_285_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
lean_inc_ref_n(v___x_292_, 2);
v___x_293_ = l_Lean_Syntax_node2(v___x_285_, v___x_289_, v___x_292_, v___x_281_);
v___x_294_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__10));
v___x_295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_285_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__12));
v___x_297_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__14));
v___x_298_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__5));
v___x_299_ = l_Lean_SourceInfo_fromRef(v_tk_279_, v___x_275_);
lean_dec(v_tk_279_);
v___x_300_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__15));
v___x_301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Lean_Syntax_node1(v___x_285_, v___x_298_, v___x_301_);
v___x_303_ = l_Lean_Syntax_node2(v___x_285_, v___x_297_, v___x_302_, v___x_292_);
v___x_304_ = l_Lean_Syntax_node1(v___x_285_, v___x_290_, v___x_303_);
v___x_305_ = l_Lean_Syntax_node1(v___x_285_, v___x_296_, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__16));
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_285_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_Syntax_node2(v___x_285_, v___x_290_, v___x_307_, v___x_283_);
v___x_309_ = l_Lean_Syntax_node6(v___x_285_, v___x_286_, v___x_288_, v___x_293_, v___x_295_, v___x_305_, v___x_292_, v___x_308_);
v___x_310_ = l_Lean_Elab_Do_elabDoElem(v___x_309_, v_dec_265_, v___x_275_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
return v___x_310_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoUnless_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_264_ = stack[0].m_obj;
lean_object* v_dec_265_ = stack[1].m_obj;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_a_270_ = stack[6].m_obj;
lean_object* v_a_271_ = stack[7].m_obj;
lean_object* v_a_272_ = stack[8].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Lean_Elab_Do_elabDoUnless(v_stx_264_, v_dec_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoUnless___boxed(lean_object* v_stx_312_, lean_object* v_dec_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_Do_elabDoUnless(v_stx_312_, v_dec_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec_ref(v_a_314_);
return v_res_322_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1(){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_330_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_331_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__1));
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1));
v___x_333_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoUnless___boxed), 10, 0);
v___x_334_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_330_, v___x_331_, v___x_332_, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_335_;
v_res_335_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
return v_res_337_;
}
}
lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0(lean_object* v___x_341_, lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v_a_345_, uint8_t v___x_346_, lean_object* v_body_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_ref_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_ref_356_ = lean_ctor_get(v___y_353_, 2);
v___x_357_ = 0;
v___x_358_ = l_Lean_SourceInfo_fromRef(v_ref_356_, v___x_357_);
v___x_359_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0));
v___x_360_ = l_Lean_Name_mkStr4(v___x_341_, v___x_342_, v___x_343_, v___x_359_);
v___x_361_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1));
lean_inc_n(v___x_358_, 2);
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_358_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2));
v___x_364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_358_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_Lean_Syntax_node4(v___x_358_, v___x_360_, v___x_362_, v___x_344_, v___x_364_, v_body_347_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v_a_345_);
v___x_367_ = l_Lean_Elab_Term_elabTerm(v___x_365_, v___x_366_, v___x_346_, v___x_346_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoDbgTrace___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_341_ = stack[0].m_obj;
lean_object* v___x_342_ = stack[1].m_obj;
lean_object* v___x_343_ = stack[2].m_obj;
lean_object* v___x_344_ = stack[3].m_obj;
lean_object* v_a_345_ = stack[4].m_obj;
uint8_t v___x_346_ = stack[5].m_num;
lean_object* v_body_347_ = stack[6].m_obj;
lean_object* v___y_348_ = stack[7].m_obj;
lean_object* v___y_349_ = stack[8].m_obj;
lean_object* v___y_350_ = stack[9].m_obj;
lean_object* v___y_351_ = stack[10].m_obj;
lean_object* v___y_352_ = stack[11].m_obj;
lean_object* v___y_353_ = stack[12].m_obj;
lean_object* v___y_354_ = stack[13].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0(v___x_341_, v___x_342_, v___x_343_, v___x_344_, v_a_345_, v___x_346_, v_body_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed(lean_object* v___x_369_, lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v___x_372_, lean_object* v_a_373_, lean_object* v___x_374_, lean_object* v_body_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_3550__boxed_384_; lean_object* v_res_385_; 
v___x_3550__boxed_384_ = lean_unbox(v___x_374_);
v_res_385_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0(v___x_369_, v___x_370_, v___x_371_, v___x_372_, v_a_373_, v___x_3550__boxed_384_, v_body_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_385_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoDbgTrace___closed__4(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___closed__3));
v___x_396_ = l_Lean_MessageData_ofFormat(v___x_395_);
return v___x_396_;
}
}
lean_object* l_Lean_Elab_Do_elabDoDbgTrace(lean_object* v_stx_397_, lean_object* v_dec_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_407_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__0));
v___x_408_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__1));
v___x_409_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__2));
v___x_410_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___closed__1));
lean_inc(v_stx_397_);
v___x_411_ = l_Lean_Syntax_isOfKind(v_stx_397_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec_ref(v_dec_398_);
lean_dec(v_stx_397_);
v___x_412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_412_;
}
else
{
lean_object* v_doBlockResultType_413_; lean_object* v___x_414_; lean_object* v_tk_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_doBlockResultType_413_ = lean_ctor_get(v_a_399_, 3);
v___x_414_ = lean_unsigned_to_nat(0u);
v_tk_415_ = l_Lean_Syntax_getArg(v_stx_397_, v___x_414_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = l_Lean_Syntax_getArg(v_stx_397_, v___x_416_);
lean_dec(v_stx_397_);
lean_inc_ref(v_doBlockResultType_413_);
v___x_418_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_413_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; lean_object* v___f_421_; lean_object* v___x_422_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = lean_box(v___x_411_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___f_421_, 0, v___x_407_);
lean_closure_set(v___f_421_, 1, v___x_408_);
lean_closure_set(v___f_421_, 2, v___x_409_);
lean_closure_set(v___f_421_, 3, v___x_417_);
lean_closure_set(v___f_421_, 4, v_a_419_);
lean_closure_set(v___f_421_, 5, v___x_420_);
v___x_422_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_398_, v_tk_415_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_tk_415_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = lean_obj_once(&l_Lean_Elab_Do_elabDoDbgTrace___closed__4, &l_Lean_Elab_Do_elabDoDbgTrace___closed__4_once, _init_l_Lean_Elab_Do_elabDoDbgTrace___closed__4);
v___x_425_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_425_, 0, v_a_423_);
v___x_426_ = lean_box(0);
v___x_427_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_424_, v___x_425_, v___f_421_, v___x_426_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_427_;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v___f_421_);
v_a_428_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_422_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_422_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_dec(v___x_417_);
lean_dec(v_tk_415_);
lean_dec_ref(v_dec_398_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoDbgTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_397_ = stack[0].m_obj;
lean_object* v_dec_398_ = stack[1].m_obj;
lean_object* v_a_399_ = stack[2].m_obj;
lean_object* v_a_400_ = stack[3].m_obj;
lean_object* v_a_401_ = stack[4].m_obj;
lean_object* v_a_402_ = stack[5].m_obj;
lean_object* v_a_403_ = stack[6].m_obj;
lean_object* v_a_404_ = stack[7].m_obj;
lean_object* v_a_405_ = stack[8].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_Elab_Do_elabDoDbgTrace(v_stx_397_, v_dec_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___boxed(lean_object* v_stx_437_, lean_object* v_dec_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Elab_Do_elabDoDbgTrace(v_stx_437_, v_dec_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec_ref(v_a_439_);
return v_res_447_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1(){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_456_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___closed__1));
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1));
v___x_458_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDbgTrace___boxed), 10, 0);
v___x_459_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_455_, v___x_456_, v___x_457_, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_460_;
v_res_460_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___boxed(lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
return v_res_462_;
}
}
lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0(lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v___x_468_, lean_object* v_a_469_, uint8_t v___x_470_, lean_object* v_body_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_ref_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_ref_480_ = lean_ctor_get(v___y_477_, 2);
v___x_481_ = 0;
v___x_482_ = l_Lean_SourceInfo_fromRef(v_ref_480_, v___x_481_);
v___x_483_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0));
v___x_484_ = l_Lean_Name_mkStr4(v___x_465_, v___x_466_, v___x_467_, v___x_483_);
v___x_485_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1));
lean_inc_n(v___x_482_, 2);
v___x_486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_482_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2));
v___x_488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_482_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_Syntax_node4(v___x_482_, v___x_484_, v___x_486_, v___x_468_, v___x_488_, v_body_471_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_a_469_);
v___x_491_ = l_Lean_Elab_Term_elabTerm(v___x_489_, v___x_490_, v___x_470_, v___x_470_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_491_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoAssert___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_465_ = stack[0].m_obj;
lean_object* v___x_466_ = stack[1].m_obj;
lean_object* v___x_467_ = stack[2].m_obj;
lean_object* v___x_468_ = stack[3].m_obj;
lean_object* v_a_469_ = stack[4].m_obj;
uint8_t v___x_470_ = stack[5].m_num;
lean_object* v_body_471_ = stack[6].m_obj;
lean_object* v___y_472_ = stack[7].m_obj;
lean_object* v___y_473_ = stack[8].m_obj;
lean_object* v___y_474_ = stack[9].m_obj;
lean_object* v___y_475_ = stack[10].m_obj;
lean_object* v___y_476_ = stack[11].m_obj;
lean_object* v___y_477_ = stack[12].m_obj;
lean_object* v___y_478_ = stack[13].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Lean_Elab_Do_elabDoAssert___lam__0(v___x_465_, v___x_466_, v___x_467_, v___x_468_, v_a_469_, v___x_470_, v_body_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0___boxed(lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v_a_497_, lean_object* v___x_498_, lean_object* v_body_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_3539__boxed_508_; lean_object* v_res_509_; 
v___x_3539__boxed_508_ = lean_unbox(v___x_498_);
v_res_509_ = l_Lean_Elab_Do_elabDoAssert___lam__0(v___x_493_, v___x_494_, v___x_495_, v___x_496_, v_a_497_, v___x_3539__boxed_508_, v_body_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoAssert___closed__4(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___closed__3));
v___x_520_ = l_Lean_MessageData_ofFormat(v___x_519_);
return v___x_520_;
}
}
lean_object* l_Lean_Elab_Do_elabDoAssert(lean_object* v_stx_521_, lean_object* v_dec_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_531_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__0));
v___x_532_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__1));
v___x_533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__2));
v___x_534_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___closed__1));
lean_inc(v_stx_521_);
v___x_535_ = l_Lean_Syntax_isOfKind(v_stx_521_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec_ref(v_dec_522_);
lean_dec(v_stx_521_);
v___x_536_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_536_;
}
else
{
lean_object* v_doBlockResultType_537_; lean_object* v___x_538_; lean_object* v_tk_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_doBlockResultType_537_ = lean_ctor_get(v_a_523_, 3);
v___x_538_ = lean_unsigned_to_nat(0u);
v_tk_539_ = l_Lean_Syntax_getArg(v_stx_521_, v___x_538_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = l_Lean_Syntax_getArg(v_stx_521_, v___x_540_);
lean_dec(v_stx_521_);
lean_inc_ref(v_doBlockResultType_537_);
v___x_542_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_537_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_box(v___x_535_);
v___f_545_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoAssert___lam__0___boxed), 15, 6);
lean_closure_set(v___f_545_, 0, v___x_531_);
lean_closure_set(v___f_545_, 1, v___x_532_);
lean_closure_set(v___f_545_, 2, v___x_533_);
lean_closure_set(v___f_545_, 3, v___x_541_);
lean_closure_set(v___f_545_, 4, v_a_543_);
lean_closure_set(v___f_545_, 5, v___x_544_);
v___x_546_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_522_, v_tk_539_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_tk_539_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_obj_once(&l_Lean_Elab_Do_elabDoAssert___closed__4, &l_Lean_Elab_Do_elabDoAssert___closed__4_once, _init_l_Lean_Elab_Do_elabDoAssert___closed__4);
v___x_549_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_549_, 0, v_a_547_);
v___x_550_ = lean_box(0);
v___x_551_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_548_, v___x_549_, v___f_545_, v___x_550_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
return v___x_551_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec_ref(v___f_545_);
v_a_552_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_546_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_546_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_dec(v___x_541_);
lean_dec(v_tk_539_);
lean_dec_ref(v_dec_522_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoAssert_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_521_ = stack[0].m_obj;
lean_object* v_dec_522_ = stack[1].m_obj;
lean_object* v_a_523_ = stack[2].m_obj;
lean_object* v_a_524_ = stack[3].m_obj;
lean_object* v_a_525_ = stack[4].m_obj;
lean_object* v_a_526_ = stack[5].m_obj;
lean_object* v_a_527_ = stack[6].m_obj;
lean_object* v_a_528_ = stack[7].m_obj;
lean_object* v_a_529_ = stack[8].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lean_Elab_Do_elabDoAssert(v_stx_521_, v_dec_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___boxed(lean_object* v_stx_561_, lean_object* v_dec_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_Do_elabDoAssert(v_stx_561_, v_dec_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_571_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1(){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_579_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___closed__1));
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1));
v___x_582_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoAssert___boxed), 10, 0);
v___x_583_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_579_, v___x_580_, v___x_581_, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_584_;
v_res_584_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
return v_res_586_;
}
}
lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0(lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v_a_593_, uint8_t v___x_594_, lean_object* v_body_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_ref_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_ref_604_ = lean_ctor_get(v___y_601_, 2);
v___x_605_ = 0;
v___x_606_ = l_Lean_SourceInfo_fromRef(v_ref_604_, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0));
v___x_608_ = l_Lean_Name_mkStr4(v___x_589_, v___x_590_, v___x_591_, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1));
lean_inc_n(v___x_606_, 2);
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_606_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2));
v___x_612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_606_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Lean_Syntax_node4(v___x_606_, v___x_608_, v___x_610_, v___x_592_, v___x_612_, v_body_595_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_a_593_);
v___x_615_ = l_Lean_Elab_Term_elabTerm(v___x_613_, v___x_614_, v___x_594_, v___x_594_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_615_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoDebugAssert___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_589_ = stack[0].m_obj;
lean_object* v___x_590_ = stack[1].m_obj;
lean_object* v___x_591_ = stack[2].m_obj;
lean_object* v___x_592_ = stack[3].m_obj;
lean_object* v_a_593_ = stack[4].m_obj;
uint8_t v___x_594_ = stack[5].m_num;
lean_object* v_body_595_ = stack[6].m_obj;
lean_object* v___y_596_ = stack[7].m_obj;
lean_object* v___y_597_ = stack[8].m_obj;
lean_object* v___y_598_ = stack[9].m_obj;
lean_object* v___y_599_ = stack[10].m_obj;
lean_object* v___y_600_ = stack[11].m_obj;
lean_object* v___y_601_ = stack[12].m_obj;
lean_object* v___y_602_ = stack[13].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Lean_Elab_Do_elabDoDebugAssert___lam__0(v___x_589_, v___x_590_, v___x_591_, v___x_592_, v_a_593_, v___x_594_, v_body_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed(lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___x_620_, lean_object* v_a_621_, lean_object* v___x_622_, lean_object* v_body_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_3539__boxed_632_; lean_object* v_res_633_; 
v___x_3539__boxed_632_ = lean_unbox(v___x_622_);
v_res_633_ = l_Lean_Elab_Do_elabDoDebugAssert___lam__0(v___x_617_, v___x_618_, v___x_619_, v___x_620_, v_a_621_, v___x_3539__boxed_632_, v_body_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_633_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoDebugAssert___closed__4(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___closed__3));
v___x_644_ = l_Lean_MessageData_ofFormat(v___x_643_);
return v___x_644_;
}
}
lean_object* l_Lean_Elab_Do_elabDoDebugAssert(lean_object* v_stx_645_, lean_object* v_dec_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_655_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__0));
v___x_656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__1));
v___x_657_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__2));
v___x_658_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___closed__1));
lean_inc(v_stx_645_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_stx_645_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_dec_646_);
lean_dec(v_stx_645_);
v___x_660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_660_;
}
else
{
lean_object* v_doBlockResultType_661_; lean_object* v___x_662_; lean_object* v_tk_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_doBlockResultType_661_ = lean_ctor_get(v_a_647_, 3);
v___x_662_ = lean_unsigned_to_nat(0u);
v_tk_663_ = l_Lean_Syntax_getArg(v_stx_645_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = l_Lean_Syntax_getArg(v_stx_645_, v___x_664_);
lean_dec(v_stx_645_);
lean_inc_ref(v_doBlockResultType_661_);
v___x_666_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_661_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___f_669_; lean_object* v___x_670_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_box(v___x_659_);
v___f_669_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed), 15, 6);
lean_closure_set(v___f_669_, 0, v___x_655_);
lean_closure_set(v___f_669_, 1, v___x_656_);
lean_closure_set(v___f_669_, 2, v___x_657_);
lean_closure_set(v___f_669_, 3, v___x_665_);
lean_closure_set(v___f_669_, 4, v_a_667_);
lean_closure_set(v___f_669_, 5, v___x_668_);
v___x_670_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_646_, v_tk_663_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_tk_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_obj_once(&l_Lean_Elab_Do_elabDoDebugAssert___closed__4, &l_Lean_Elab_Do_elabDoDebugAssert___closed__4_once, _init_l_Lean_Elab_Do_elabDoDebugAssert___closed__4);
v___x_673_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_673_, 0, v_a_671_);
v___x_674_ = lean_box(0);
v___x_675_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_672_, v___x_673_, v___f_669_, v___x_674_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_675_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___f_669_);
v_a_676_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_670_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_670_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_dec(v___x_665_);
lean_dec(v_tk_663_);
lean_dec_ref(v_dec_646_);
return v___x_666_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoDebugAssert_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_645_ = stack[0].m_obj;
lean_object* v_dec_646_ = stack[1].m_obj;
lean_object* v_a_647_ = stack[2].m_obj;
lean_object* v_a_648_ = stack[3].m_obj;
lean_object* v_a_649_ = stack[4].m_obj;
lean_object* v_a_650_ = stack[5].m_obj;
lean_object* v_a_651_ = stack[6].m_obj;
lean_object* v_a_652_ = stack[7].m_obj;
lean_object* v_a_653_ = stack[8].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Elab_Do_elabDoDebugAssert(v_stx_645_, v_dec_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___boxed(lean_object* v_stx_685_, lean_object* v_dec_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_Do_elabDoDebugAssert(v_stx_685_, v_dec_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_695_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1(){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_703_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_704_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___closed__1));
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1));
v___x_706_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDebugAssert___boxed), 10, 0);
v___x_707_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_703_, v___x_704_, v___x_705_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_708_;
v_res_708_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
return v_res_710_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Misc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Forward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Misc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Misc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Forward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Misc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Misc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Misc(builtin);
}
#ifdef __cplusplus
}
#endif
