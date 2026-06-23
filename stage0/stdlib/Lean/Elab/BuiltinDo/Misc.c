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
lean_object* l_Array_mkArray0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___boxed(lean_object* v_00_u03b1_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(v_00_u03b1_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoSkip(lean_object* v_stx_40_, lean_object* v_dec_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__5));
lean_inc(v_stx_40_);
v___x_51_ = l_Lean_Syntax_isOfKind(v_stx_40_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec_ref(v_dec_41_);
lean_dec(v_stx_40_);
v___x_52_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v_tk_54_; lean_object* v___x_55_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v_tk_54_ = l_Lean_Syntax_getArg(v_stx_40_, v___x_53_);
lean_dec(v_stx_40_);
v___x_55_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_41_, v_tk_54_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
lean_dec(v_tk_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v___x_57_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
lean_dec_ref_known(v___x_55_, 1);
v___x_57_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_56_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
return v___x_57_;
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_55_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_55_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoSkip___boxed(lean_object* v_stx_66_, lean_object* v_dec_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Elab_Do_elabDoSkip(v_stx_66_, v_dec_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec_ref(v_a_68_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_87_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__5));
v___x_88_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3));
v___x_89_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSkip___boxed), 10, 0);
v___x_90_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_86_, v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoExpr(lean_object* v_stx_99_, lean_object* v_dec_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_Do_elabDoExpr___closed__1));
lean_inc(v_stx_99_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_stx_99_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_dec_100_);
lean_dec(v_stx_99_);
v___x_111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v_e_113_; lean_object* v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v_e_113_ = l_Lean_Syntax_getArg(v_stx_99_, v___x_112_);
lean_dec(v_stx_99_);
lean_inc_ref(v_dec_100_);
lean_inc(v_e_113_);
v___x_114_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_113_, v_dec_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_137_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_137_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
if (lean_obj_tag(v_a_115_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_121_; 
lean_dec(v_e_113_);
lean_dec_ref(v_dec_100_);
v_val_119_ = lean_ctor_get(v_a_115_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v_a_115_, 1);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_val_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_val_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
else
{
lean_object* v_resultType_123_; lean_object* v___x_124_; 
lean_del_object(v___x_117_);
lean_dec(v_a_115_);
v_resultType_123_ = lean_ctor_get(v_dec_100_, 1);
lean_inc_ref(v_resultType_123_);
v___x_124_ = l_Lean_Elab_Do_mkMonadApp(v_resultType_123_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_136_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_136_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_136_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_136_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 1);
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_135_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(0);
v___x_132_ = l_Lean_Elab_Term_elabTermEnsuringType(v_e_113_, v___x_130_, v___x_110_, v___x_110_, v___x_131_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_134_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_132_, 1);
v___x_134_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_dec_100_, v_a_133_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_134_;
}
else
{
lean_dec_ref(v_dec_100_);
return v___x_132_;
}
}
}
}
else
{
lean_dec(v_e_113_);
lean_dec_ref(v_dec_100_);
return v___x_124_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_e_113_);
lean_dec_ref(v_dec_100_);
v_a_138_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_114_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_114_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoExpr___boxed(lean_object* v_stx_146_, lean_object* v_dec_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Elab_Do_elabDoExpr(v_stx_146_, v_dec_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1(){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_165_ = ((lean_object*)(l_Lean_Elab_Do_elabDoExpr___closed__1));
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1));
v___x_167_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoExpr___boxed), 10, 0);
v___x_168_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_164_, v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoNested(lean_object* v_stx_177_, lean_object* v_dec_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Elab_Do_elabDoNested___closed__1));
lean_inc(v_stx_177_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_stx_177_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
lean_dec_ref(v_dec_178_);
lean_dec(v_stx_177_);
v___x_189_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = l_Lean_Syntax_getArg(v_stx_177_, v___x_190_);
lean_dec(v_stx_177_);
v___x_192_ = l_Lean_Elab_Do_elabDoSeq(v___x_191_, v_dec_178_, v___x_188_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoNested___boxed(lean_object* v_stx_193_, lean_object* v_dec_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_Do_elabDoNested(v_stx_193_, v_dec_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1(){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_211_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_212_ = ((lean_object*)(l_Lean_Elab_Do_elabDoNested___closed__1));
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1));
v___x_214_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoNested___boxed), 10, 0);
v___x_215_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_211_, v___x_212_, v___x_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___boxed(lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoUnless___closed__9(void){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Array_mkArray0(lean_box(0));
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoUnless(lean_object* v_stx_256_, lean_object* v_dec_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__1));
lean_inc(v_stx_256_);
v___x_267_ = l_Lean_Syntax_isOfKind(v_stx_256_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec_ref(v_dec_257_);
lean_dec(v_stx_256_);
v___x_268_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_268_;
}
else
{
lean_object* v_ref_269_; lean_object* v___x_270_; lean_object* v_tk_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_ref_269_ = lean_ctor_get(v_a_263_, 5);
v___x_270_ = lean_unsigned_to_nat(0u);
v_tk_271_ = l_Lean_Syntax_getArg(v_stx_256_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = l_Lean_Syntax_getArg(v_stx_256_, v___x_272_);
v___x_274_ = lean_unsigned_to_nat(3u);
v___x_275_ = l_Lean_Syntax_getArg(v_stx_256_, v___x_274_);
lean_dec(v_stx_256_);
v___x_276_ = 0;
v___x_277_ = l_Lean_SourceInfo_fromRef(v_ref_269_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__3));
v___x_279_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__4));
lean_inc_n(v___x_277_, 10);
v___x_280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_277_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__6));
v___x_282_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__8));
v___x_283_ = lean_obj_once(&l_Lean_Elab_Do_elabDoUnless___closed__9, &l_Lean_Elab_Do_elabDoUnless___closed__9_once, _init_l_Lean_Elab_Do_elabDoUnless___closed__9);
v___x_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_284_, 0, v___x_277_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
lean_ctor_set(v___x_284_, 2, v___x_283_);
lean_inc_ref_n(v___x_284_, 2);
v___x_285_ = l_Lean_Syntax_node2(v___x_277_, v___x_281_, v___x_284_, v___x_273_);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__10));
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_277_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__12));
v___x_289_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__14));
v___x_290_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__5));
v___x_291_ = l_Lean_SourceInfo_fromRef(v_tk_271_, v___x_267_);
lean_dec(v_tk_271_);
v___x_292_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__15));
v___x_293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l_Lean_Syntax_node1(v___x_277_, v___x_290_, v___x_293_);
v___x_295_ = l_Lean_Syntax_node2(v___x_277_, v___x_289_, v___x_294_, v___x_284_);
v___x_296_ = l_Lean_Syntax_node1(v___x_277_, v___x_282_, v___x_295_);
v___x_297_ = l_Lean_Syntax_node1(v___x_277_, v___x_288_, v___x_296_);
v___x_298_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__16));
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_277_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = l_Lean_Syntax_node2(v___x_277_, v___x_282_, v___x_299_, v___x_275_);
v___x_301_ = l_Lean_Syntax_node6(v___x_277_, v___x_278_, v___x_280_, v___x_285_, v___x_287_, v___x_297_, v___x_284_, v___x_300_);
v___x_302_ = l_Lean_Elab_Do_elabDoElem(v___x_301_, v_dec_257_, v___x_267_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoUnless___boxed(lean_object* v_stx_303_, lean_object* v_dec_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Elab_Do_elabDoUnless(v_stx_303_, v_dec_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1(){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_322_ = ((lean_object*)(l_Lean_Elab_Do_elabDoUnless___closed__1));
v___x_323_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1));
v___x_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoUnless___boxed), 10, 0);
v___x_325_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_321_, v___x_322_, v___x_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___boxed(lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0(lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v___x_333_, lean_object* v___x_334_, lean_object* v_a_335_, uint8_t v___x_336_, lean_object* v_body_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_ref_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_ref_346_ = lean_ctor_get(v___y_343_, 5);
v___x_347_ = 0;
v___x_348_ = l_Lean_SourceInfo_fromRef(v_ref_346_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0));
v___x_350_ = l_Lean_Name_mkStr4(v___x_331_, v___x_332_, v___x_333_, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1));
lean_inc_n(v___x_348_, 2);
v___x_352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_348_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_348_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_Syntax_node4(v___x_348_, v___x_350_, v___x_352_, v___x_334_, v___x_354_, v_body_337_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_a_335_);
v___x_357_ = l_Lean_Elab_Term_elabTerm(v___x_355_, v___x_356_, v___x_336_, v___x_336_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed(lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_a_362_, lean_object* v___x_363_, lean_object* v_body_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v___x_3724__boxed_373_; lean_object* v_res_374_; 
v___x_3724__boxed_373_ = lean_unbox(v___x_363_);
v_res_374_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0(v___x_358_, v___x_359_, v___x_360_, v___x_361_, v_a_362_, v___x_3724__boxed_373_, v_body_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoDbgTrace___closed__4(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___closed__3));
v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace(lean_object* v_stx_386_, lean_object* v_dec_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_396_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__0));
v___x_397_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__1));
v___x_398_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__2));
v___x_399_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___closed__1));
lean_inc(v_stx_386_);
v___x_400_ = l_Lean_Syntax_isOfKind(v_stx_386_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v_dec_387_);
lean_dec(v_stx_386_);
v___x_401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_401_;
}
else
{
lean_object* v_doBlockResultType_402_; lean_object* v___x_403_; 
v_doBlockResultType_402_ = lean_ctor_get(v_a_388_, 3);
lean_inc_ref(v_doBlockResultType_402_);
v___x_403_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_402_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; lean_object* v_tk_406_; lean_object* v___x_407_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = lean_unsigned_to_nat(0u);
v_tk_406_ = l_Lean_Syntax_getArg(v_stx_386_, v___x_405_);
v___x_407_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_387_, v_tk_406_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_tk_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = l_Lean_Syntax_getArg(v_stx_386_, v___x_409_);
lean_dec(v_stx_386_);
v___x_411_ = lean_box(v___x_400_);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___f_412_, 0, v___x_396_);
lean_closure_set(v___f_412_, 1, v___x_397_);
lean_closure_set(v___f_412_, 2, v___x_398_);
lean_closure_set(v___f_412_, 3, v___x_410_);
lean_closure_set(v___f_412_, 4, v_a_404_);
lean_closure_set(v___f_412_, 5, v___x_411_);
v___x_413_ = lean_obj_once(&l_Lean_Elab_Do_elabDoDbgTrace___closed__4, &l_Lean_Elab_Do_elabDoDbgTrace___closed__4_once, _init_l_Lean_Elab_Do_elabDoDbgTrace___closed__4);
v___x_414_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_414_, 0, v_a_408_);
v___x_415_ = lean_box(0);
v___x_416_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_413_, v___x_414_, v___f_412_, v___x_415_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
return v___x_416_;
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_a_404_);
lean_dec(v_stx_386_);
v_a_417_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_dec_ref(v_dec_387_);
lean_dec(v_stx_386_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDbgTrace___boxed(lean_object* v_stx_425_, lean_object* v_dec_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Elab_Do_elabDoDbgTrace(v_stx_425_, v_dec_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1(){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_443_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_444_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___closed__1));
v___x_445_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1));
v___x_446_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDbgTrace___boxed), 10, 0);
v___x_447_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_443_, v___x_444_, v___x_445_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___boxed(lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0(lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v_a_456_, uint8_t v___x_457_, lean_object* v_body_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_ref_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_ref_467_ = lean_ctor_get(v___y_464_, 5);
v___x_468_ = 0;
v___x_469_ = l_Lean_SourceInfo_fromRef(v_ref_467_, v___x_468_);
v___x_470_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0));
v___x_471_ = l_Lean_Name_mkStr4(v___x_452_, v___x_453_, v___x_454_, v___x_470_);
v___x_472_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1));
lean_inc_n(v___x_469_, 2);
v___x_473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_469_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2));
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_469_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_Syntax_node4(v___x_469_, v___x_471_, v___x_473_, v___x_455_, v___x_475_, v_body_458_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_a_456_);
v___x_478_ = l_Lean_Elab_Term_elabTerm(v___x_476_, v___x_477_, v___x_457_, v___x_457_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___lam__0___boxed(lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_a_483_, lean_object* v___x_484_, lean_object* v_body_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
uint8_t v___x_3713__boxed_494_; lean_object* v_res_495_; 
v___x_3713__boxed_494_ = lean_unbox(v___x_484_);
v_res_495_ = l_Lean_Elab_Do_elabDoAssert___lam__0(v___x_479_, v___x_480_, v___x_481_, v___x_482_, v_a_483_, v___x_3713__boxed_494_, v_body_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_495_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoAssert___closed__4(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___closed__3));
v___x_506_ = l_Lean_MessageData_ofFormat(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert(lean_object* v_stx_507_, lean_object* v_dec_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__0));
v___x_518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__1));
v___x_519_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__2));
v___x_520_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___closed__1));
lean_inc(v_stx_507_);
v___x_521_ = l_Lean_Syntax_isOfKind(v_stx_507_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_dec_508_);
lean_dec(v_stx_507_);
v___x_522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_522_;
}
else
{
lean_object* v_doBlockResultType_523_; lean_object* v___x_524_; 
v_doBlockResultType_523_ = lean_ctor_get(v_a_509_, 3);
lean_inc_ref(v_doBlockResultType_523_);
v___x_524_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_523_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v_tk_527_; lean_object* v___x_528_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = lean_unsigned_to_nat(0u);
v_tk_527_ = l_Lean_Syntax_getArg(v_stx_507_, v___x_526_);
v___x_528_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_508_, v_tk_527_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_tk_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = l_Lean_Syntax_getArg(v_stx_507_, v___x_530_);
lean_dec(v_stx_507_);
v___x_532_ = lean_box(v___x_521_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoAssert___lam__0___boxed), 15, 6);
lean_closure_set(v___f_533_, 0, v___x_517_);
lean_closure_set(v___f_533_, 1, v___x_518_);
lean_closure_set(v___f_533_, 2, v___x_519_);
lean_closure_set(v___f_533_, 3, v___x_531_);
lean_closure_set(v___f_533_, 4, v_a_525_);
lean_closure_set(v___f_533_, 5, v___x_532_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_Do_elabDoAssert___closed__4, &l_Lean_Elab_Do_elabDoAssert___closed__4_once, _init_l_Lean_Elab_Do_elabDoAssert___closed__4);
v___x_535_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_535_, 0, v_a_529_);
v___x_536_ = lean_box(0);
v___x_537_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_534_, v___x_535_, v___f_533_, v___x_536_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
return v___x_537_;
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_a_525_);
lean_dec(v_stx_507_);
v_a_538_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_528_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_528_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_dec_ref(v_dec_508_);
lean_dec(v_stx_507_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoAssert___boxed(lean_object* v_stx_546_, lean_object* v_dec_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_Do_elabDoAssert(v_stx_546_, v_dec_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec_ref(v_a_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1(){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_564_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_565_ = ((lean_object*)(l_Lean_Elab_Do_elabDoAssert___closed__1));
v___x_566_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1));
v___x_567_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoAssert___boxed), 10, 0);
v___x_568_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_564_, v___x_565_, v___x_566_, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___boxed(lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0(lean_object* v___x_573_, lean_object* v___x_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v_a_577_, uint8_t v___x_578_, lean_object* v_body_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_ref_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_ref_588_ = lean_ctor_get(v___y_585_, 5);
v___x_589_ = 0;
v___x_590_ = l_Lean_SourceInfo_fromRef(v_ref_588_, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0));
v___x_592_ = l_Lean_Name_mkStr4(v___x_573_, v___x_574_, v___x_575_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1));
lean_inc_n(v___x_590_, 2);
v___x_594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_590_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2));
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_590_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_Syntax_node4(v___x_590_, v___x_592_, v___x_594_, v___x_576_, v___x_596_, v_body_579_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_a_577_);
v___x_599_ = l_Lean_Elab_Term_elabTerm(v___x_597_, v___x_598_, v___x_578_, v___x_578_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed(lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v___x_603_, lean_object* v_a_604_, lean_object* v___x_605_, lean_object* v_body_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_3713__boxed_615_; lean_object* v_res_616_; 
v___x_3713__boxed_615_ = lean_unbox(v___x_605_);
v_res_616_ = l_Lean_Elab_Do_elabDoDebugAssert___lam__0(v___x_600_, v___x_601_, v___x_602_, v___x_603_, v_a_604_, v___x_3713__boxed_615_, v_body_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoDebugAssert___closed__4(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___closed__3));
v___x_627_ = l_Lean_MessageData_ofFormat(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert(lean_object* v_stx_628_, lean_object* v_dec_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_638_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__0));
v___x_639_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__1));
v___x_640_ = ((lean_object*)(l_Lean_Elab_Do_elabDoSkip___closed__2));
v___x_641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___closed__1));
lean_inc(v_stx_628_);
v___x_642_ = l_Lean_Syntax_isOfKind(v_stx_628_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_dec_629_);
lean_dec(v_stx_628_);
v___x_643_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
return v___x_643_;
}
else
{
lean_object* v_doBlockResultType_644_; lean_object* v___x_645_; 
v_doBlockResultType_644_ = lean_ctor_get(v_a_630_, 3);
lean_inc_ref(v_doBlockResultType_644_);
v___x_645_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_644_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v_tk_648_; lean_object* v___x_649_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = lean_unsigned_to_nat(0u);
v_tk_648_ = l_Lean_Syntax_getArg(v_stx_628_, v___x_647_);
v___x_649_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_629_, v_tk_648_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_tk_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = l_Lean_Syntax_getArg(v_stx_628_, v___x_651_);
lean_dec(v_stx_628_);
v___x_653_ = lean_box(v___x_642_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed), 15, 6);
lean_closure_set(v___f_654_, 0, v___x_638_);
lean_closure_set(v___f_654_, 1, v___x_639_);
lean_closure_set(v___f_654_, 2, v___x_640_);
lean_closure_set(v___f_654_, 3, v___x_652_);
lean_closure_set(v___f_654_, 4, v_a_646_);
lean_closure_set(v___f_654_, 5, v___x_653_);
v___x_655_ = lean_obj_once(&l_Lean_Elab_Do_elabDoDebugAssert___closed__4, &l_Lean_Elab_Do_elabDoDebugAssert___closed__4_once, _init_l_Lean_Elab_Do_elabDoDebugAssert___closed__4);
v___x_656_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_656_, 0, v_a_650_);
v___x_657_ = lean_box(0);
v___x_658_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_655_, v___x_656_, v___f_654_, v___x_657_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_658_;
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_a_646_);
lean_dec(v_stx_628_);
v_a_659_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_649_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_649_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_dec_ref(v_dec_629_);
lean_dec(v_stx_628_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoDebugAssert___boxed(lean_object* v_stx_667_, lean_object* v_dec_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_Do_elabDoDebugAssert(v_stx_667_, v_dec_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v_a_669_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1(){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_685_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_686_ = ((lean_object*)(l_Lean_Elab_Do_elabDoDebugAssert___closed__1));
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1));
v___x_688_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoDebugAssert___boxed), 10, 0);
v___x_689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_685_, v___x_686_, v___x_687_, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___boxed(lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
return v_res_691_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Misc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
