// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Jump
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value;
lean_object* l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnitUnit___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoReturn"};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(171, 125, 33, 30, 123, 109, 189, 115)}};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value;
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoBreak___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "`break` must be nested inside a loop"};
static const lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoBreak___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_elabDoBreak___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___closed__1;
lean_object* l_Lean_Elab_Do_getBreakCont___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabDoBreak"};
static const lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(73, 189, 232, 124, 184, 58, 94, 132)}};
static const lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoContinue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`continue` must be nested inside a loop"};
static const lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoContinue___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoContinue___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___closed__1;
lean_object* l_Lean_Elab_Do_getContinueCont___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoContinue"};
static const lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 204, 183, 144, 89, 241, 195, 190)}};
static const lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = ((lean_object*)(l_Lean_Elab_Do_elabDoReturn___closed__4));
lean_inc(x_1);
x_29 = l_Lean_Syntax_isOfKind(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_71; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_71 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = l_Lean_Syntax_getArg(x_1, x_72);
lean_dec(x_1);
x_74 = l_Lean_Syntax_isNone(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_inc(x_73);
x_75 = l_Lean_Syntax_matchesNull(x_73, x_72);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_76 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Syntax_getArg(x_73, x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_30 = x_79;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = lean_box(0);
goto block_70;
}
}
else
{
lean_object* x_80; 
lean_dec(x_73);
x_80 = lean_box(0);
x_30 = x_80;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = lean_box(0);
goto block_70;
}
}
block_27:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_21 = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(x_2, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_11);
x_23 = lean_apply_9(x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
block_70:
{
lean_object* x_39; 
x_39 = l_Lean_Elab_Do_getReturnCont___redArg(x_31);
if (lean_obj_tag(x_39) == 0)
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Elab_Do_mkPUnitUnit___redArg(x_31);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_44);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_44);
x_45 = lean_box(0);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
x_46 = l_Lean_Elab_Term_ensureHasType(x_41, x_43, x_45, x_45, x_32, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_11 = x_40;
x_12 = x_47;
x_13 = x_31;
x_14 = x_32;
x_15 = x_33;
x_16 = x_34;
x_17 = x_35;
x_18 = x_36;
x_19 = x_37;
x_20 = lean_box(0);
goto block_27;
}
else
{
lean_dec(x_40);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
return x_46;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(0);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
x_52 = l_Lean_Elab_Term_ensureHasType(x_50, x_48, x_51, x_51, x_32, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_11 = x_40;
x_12 = x_53;
x_13 = x_31;
x_14 = x_32;
x_15 = x_33;
x_16 = x_34;
x_17 = x_35;
x_18 = x_36;
x_19 = x_37;
x_20 = lean_box(0);
goto block_27;
}
else
{
lean_dec(x_40);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
return x_52;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
return x_41;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
lean_dec_ref(x_39);
x_55 = !lean_is_exclusive(x_30);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_30, 0);
x_57 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_57);
lean_ctor_set(x_30, 0, x_57);
x_58 = lean_box(0);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
x_59 = l_Lean_Elab_Term_elabTermEnsuringType(x_56, x_30, x_29, x_29, x_58, x_32, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_11 = x_54;
x_12 = x_60;
x_13 = x_31;
x_14 = x_32;
x_15 = x_33;
x_16 = x_34;
x_17 = x_35;
x_18 = x_36;
x_19 = x_37;
x_20 = lean_box(0);
goto block_27;
}
else
{
lean_dec(x_54);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
return x_59;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_30, 0);
lean_inc(x_61);
lean_dec(x_30);
x_62 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_62);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_box(0);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
x_65 = l_Lean_Elab_Term_elabTermEnsuringType(x_61, x_63, x_29, x_29, x_64, x_32, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_11 = x_54;
x_12 = x_66;
x_13 = x_31;
x_14 = x_32;
x_15 = x_33;
x_16 = x_34;
x_17 = x_35;
x_18 = x_36;
x_19 = x_37;
x_20 = lean_box(0);
goto block_27;
}
else
{
lean_dec(x_54);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
return x_65;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_2);
x_67 = !lean_is_exclusive(x_39);
if (x_67 == 0)
{
return x_39;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
lean_dec(x_39);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoReturn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Do_doElemElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Do_elabDoReturn___closed__4));
x_4 = ((lean_object*)(l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReturn___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoBreak___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_elabDoBreak___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Do_getBreakCont___redArg(x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_13 = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_13);
x_14 = lean_apply_8(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_obj_once(&l_Lean_Elab_Do_elabDoBreak___redArg___closed__1, &l_Lean_Elab_Do_elabDoBreak___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoBreak___redArg___closed__1);
x_19 = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(x_18, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Do_elabDoBreak___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoBreak___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoBreak(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Do_doElemElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoBreak___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoContinue___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_elabDoContinue___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Do_getContinueCont___redArg(x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_13 = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_13);
x_14 = lean_apply_8(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_obj_once(&l_Lean_Elab_Do_elabDoContinue___redArg___closed__1, &l_Lean_Elab_Do_elabDoContinue___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoContinue___redArg___closed__1);
x_19 = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(x_18, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Do_elabDoContinue___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoContinue___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoContinue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Do_doElemElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoContinue___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Jump(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
