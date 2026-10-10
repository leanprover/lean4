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
lean_object* l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnitUnit___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Elab_Do_getContinueCont___redArg(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getBreakCont___redArg(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReturn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_elabDoReturn___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoReturn"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(171, 125, 33, 30, 123, 109, 189, 115)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoBreak___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "`break` must be nested inside a loop"};
static const lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoBreak___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoBreak___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabDoBreak"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(73, 189, 232, 124, 184, 58, 94, 132)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoContinue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`continue` must be nested inside a loop"};
static const lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoContinue___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoContinue___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoContinue"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 204, 183, 144, 89, 241, 195, 190)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0(void){
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___boxed(lean_object* v_00_u03b1_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(v_00_u03b1_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
lean_object* l_Lean_Elab_Do_elabDoReturn(lean_object* v_stx_40_, lean_object* v_dec_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___y_51_; lean_object* v_e_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v_e_x3f_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; 
v___x_71_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReturn___closed__4));
lean_inc(v_stx_40_);
v___x_72_ = l_Lean_Syntax_isOfKind(v_stx_40_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v_dec_41_);
lean_dec(v_stx_40_);
v___x_118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = l_Lean_Syntax_getArg(v_stx_40_, v___x_119_);
lean_dec(v_stx_40_);
v___x_121_ = l_Lean_Syntax_isNone(v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
lean_inc(v___x_120_);
v___x_122_ = l_Lean_Syntax_matchesNull(v___x_120_, v___x_119_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec(v___x_120_);
lean_dec_ref(v_dec_41_);
v___x_123_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v_e_x3f_125_; lean_object* v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v_e_x3f_125_ = l_Lean_Syntax_getArg(v___x_120_, v___x_124_);
lean_dec(v___x_120_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v_e_x3f_125_);
v_e_x3f_74_ = v___x_126_;
v___y_75_ = v_a_42_;
v___y_76_ = v_a_43_;
v___y_77_ = v_a_44_;
v___y_78_ = v_a_45_;
v___y_79_ = v_a_46_;
v___y_80_ = v_a_47_;
v___y_81_ = v_a_48_;
goto v___jp_73_;
}
}
else
{
lean_object* v___x_127_; 
lean_dec(v___x_120_);
v___x_127_ = lean_box(0);
v_e_x3f_74_ = v___x_127_;
v___y_75_ = v_a_42_;
v___y_76_ = v_a_43_;
v___y_77_ = v_a_44_;
v___y_78_ = v_a_45_;
v___y_79_ = v_a_46_;
v___y_80_ = v_a_47_;
v___y_81_ = v_a_48_;
goto v___jp_73_;
}
}
v___jp_50_:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(v_dec_41_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_k_61_; lean_object* v___x_62_; 
lean_dec_ref_known(v___x_60_, 1);
v_k_61_ = lean_ctor_get(v___y_51_, 1);
lean_inc_ref(v_k_61_);
lean_dec_ref(v___y_51_);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc_ref(v___y_53_);
v___x_62_ = lean_apply_9(v_k_61_, v_e_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, lean_box(0));
return v___x_62_;
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec_ref(v_e_52_);
lean_dec_ref(v___y_51_);
v_a_63_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_60_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_60_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
v___jp_73_:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_75_);
if (lean_obj_tag(v___x_82_) == 0)
{
if (lean_obj_tag(v_e_x3f_74_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_84_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_82_, 1);
v___x_84_ = l_Lean_Elab_Do_mkPUnitUnit___redArg(v___y_75_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_96_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_96_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_resultType_89_; lean_object* v___x_91_; 
v_resultType_89_ = lean_ctor_get(v_a_83_, 0);
lean_inc_ref(v_resultType_89_);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
lean_ctor_set(v___x_87_, 0, v_resultType_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_resultType_89_);
v___x_91_ = v_reuseFailAlloc_95_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_box(0);
v___x_93_ = l_Lean_Elab_Term_ensureHasType(v___x_91_, v_a_85_, v___x_92_, v___x_92_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v___y_51_ = v_a_83_;
v_e_52_ = v_a_94_;
v___y_53_ = v___y_75_;
v___y_54_ = v___y_76_;
v___y_55_ = v___y_77_;
v___y_56_ = v___y_78_;
v___y_57_ = v___y_79_;
v___y_58_ = v___y_80_;
v___y_59_ = v___y_81_;
goto v___jp_50_;
}
else
{
lean_dec(v_a_83_);
lean_dec_ref(v_dec_41_);
return v___x_93_;
}
}
}
}
else
{
lean_dec(v_a_83_);
lean_dec_ref(v_dec_41_);
return v___x_84_;
}
}
else
{
lean_object* v_a_97_; lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_109_; 
v_a_97_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_82_, 1);
v_val_98_ = lean_ctor_get(v_e_x3f_74_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_e_x3f_74_);
if (v_isSharedCheck_109_ == 0)
{
v___x_100_ = v_e_x3f_74_;
v_isShared_101_ = v_isSharedCheck_109_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_e_x3f_74_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_109_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_resultType_102_; lean_object* v___x_104_; 
v_resultType_102_ = lean_ctor_get(v_a_97_, 0);
lean_inc_ref(v_resultType_102_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v_resultType_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_resultType_102_);
v___x_104_ = v_reuseFailAlloc_108_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = l_Lean_Elab_Term_elabTermEnsuringType(v_val_98_, v___x_104_, v___x_72_, v___x_72_, v___x_105_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v___y_51_ = v_a_97_;
v_e_52_ = v_a_107_;
v___y_53_ = v___y_75_;
v___y_54_ = v___y_76_;
v___y_55_ = v___y_77_;
v___y_56_ = v___y_78_;
v___y_57_ = v___y_79_;
v___y_58_ = v___y_80_;
v___y_59_ = v___y_81_;
goto v___jp_50_;
}
else
{
lean_dec(v_a_97_);
lean_dec_ref(v_dec_41_);
return v___x_106_;
}
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v_e_x3f_74_);
lean_dec_ref(v_dec_41_);
v_a_110_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_82_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_82_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoReturn_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_40_ = stack[0].m_obj;
lean_object* v_dec_41_ = stack[1].m_obj;
lean_object* v_a_42_ = stack[2].m_obj;
lean_object* v_a_43_ = stack[3].m_obj;
lean_object* v_a_44_ = stack[4].m_obj;
lean_object* v_a_45_ = stack[5].m_obj;
lean_object* v_a_46_ = stack[6].m_obj;
lean_object* v_a_47_ = stack[7].m_obj;
lean_object* v_a_48_ = stack[8].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Elab_Do_elabDoReturn(v_stx_40_, v_dec_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReturn___boxed(lean_object* v_stx_129_, lean_object* v_dec_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Elab_Do_elabDoReturn(v_stx_129_, v_dec_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_139_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1(){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_149_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_150_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReturn___closed__4));
v___x_151_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3));
v___x_152_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReturn___boxed), 10, 0);
v___x_153_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_149_, v___x_150_, v___x_151_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_154_;
v_res_154_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___boxed(lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
return v_res_156_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(lean_object* v_msgData_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v_env_164_; uint8_t v___x_165_; lean_object* v_env_166_; lean_object* v___x_167_; lean_object* v_toCold_168_; lean_object* v_mctx_169_; lean_object* v_lctx_170_; lean_object* v_options_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_163_ = lean_st_ref_get(v___y_161_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v___x_165_ = 0;
v_env_166_ = l_Lean_Environment_setRecordingDeps(v_env_164_, v___x_165_);
v___x_167_ = lean_st_ref_get(v___y_159_);
v_toCold_168_ = lean_ctor_get(v___y_160_, 0);
v_mctx_169_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_mctx_169_);
lean_dec(v___x_167_);
v_lctx_170_ = lean_ctor_get(v___y_158_, 2);
v_options_171_ = lean_ctor_get(v_toCold_168_, 2);
lean_inc_ref(v_options_171_);
lean_inc_ref(v_lctx_170_);
v___x_172_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_172_, 0, v_env_166_);
lean_ctor_set(v___x_172_, 1, v_mctx_169_);
lean_ctor_set(v___x_172_, 2, v_lctx_170_);
lean_ctor_set(v___x_172_, 3, v_options_171_);
v___x_173_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_msgData_157_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_157_ = stack[0].m_obj;
lean_object* v___y_158_ = stack[1].m_obj;
lean_object* v___y_159_ = stack[2].m_obj;
lean_object* v___y_160_ = stack[3].m_obj;
lean_object* v___y_161_ = stack[4].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(v_msgData_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0___boxed(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(v_msgData_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_ref_189_; lean_object* v___x_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_ref_189_ = lean_ctor_get(v___y_186_, 2);
v___x_190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_199_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_inc(v_ref_189_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v_ref_189_);
lean_ctor_set(v___x_195_, 1, v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 1);
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_183_ = stack[0].m_obj;
lean_object* v___y_184_ = stack[1].m_obj;
lean_object* v___y_185_ = stack[2].m_obj;
lean_object* v___y_186_ = stack[3].m_obj;
lean_object* v___y_187_ = stack[4].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg___boxed(lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(v_msg_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_207_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoBreak___redArg___closed__1(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_Do_elabDoBreak___redArg___closed__0));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
lean_object* l_Lean_Elab_Do_elabDoBreak___redArg(lean_object* v_dec_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_212_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
if (lean_obj_tag(v_a_221_) == 1)
{
lean_object* v_val_222_; lean_object* v___x_223_; 
v_val_222_ = lean_ctor_get(v_a_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v_a_221_, 1);
v___x_223_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(v_dec_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
lean_dec_ref_known(v___x_223_, 1);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_224_ = lean_apply_8(v_val_222_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, lean_box(0));
return v___x_224_;
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_val_222_);
v_a_225_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_223_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_a_221_);
lean_dec_ref(v_dec_211_);
v___x_233_ = lean_obj_once(&l_Lean_Elab_Do_elabDoBreak___redArg___closed__1, &l_Lean_Elab_Do_elabDoBreak___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoBreak___redArg___closed__1);
v___x_234_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(v___x_233_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
return v___x_234_;
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_dec_211_);
v_a_235_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_220_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_220_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoBreak___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_dec_211_ = stack[0].m_obj;
lean_object* v_a_212_ = stack[1].m_obj;
lean_object* v_a_213_ = stack[2].m_obj;
lean_object* v_a_214_ = stack[3].m_obj;
lean_object* v_a_215_ = stack[4].m_obj;
lean_object* v_a_216_ = stack[5].m_obj;
lean_object* v_a_217_ = stack[6].m_obj;
lean_object* v_a_218_ = stack[7].m_obj;
lean_object* v_res_243_;
v_res_243_ = l_Lean_Elab_Do_elabDoBreak___redArg(v_dec_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___redArg___boxed(lean_object* v_dec_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Elab_Do_elabDoBreak___redArg(v_dec_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_253_;
}
}
lean_object* l_Lean_Elab_Do_elabDoBreak(lean_object* v___stx_254_, lean_object* v_dec_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Elab_Do_elabDoBreak___redArg(v_dec_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_264_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoBreak_0interp(lean_interpreter_value* stack)
{
lean_object* v___stx_254_ = stack[0].m_obj;
lean_object* v_dec_255_ = stack[1].m_obj;
lean_object* v_a_256_ = stack[2].m_obj;
lean_object* v_a_257_ = stack[3].m_obj;
lean_object* v_a_258_ = stack[4].m_obj;
lean_object* v_a_259_ = stack[5].m_obj;
lean_object* v_a_260_ = stack[6].m_obj;
lean_object* v_a_261_ = stack[7].m_obj;
lean_object* v_a_262_ = stack[8].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Elab_Do_elabDoBreak(v___stx_254_, v_dec_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoBreak___boxed(lean_object* v___stx_266_, lean_object* v_dec_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_Do_elabDoBreak(v___stx_266_, v_dec_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v___stx_266_);
return v_res_276_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(lean_object* v_00_u03b1_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(v_msg_278_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_278_ = stack[1].m_obj;
lean_object* v___y_279_ = stack[2].m_obj;
lean_object* v___y_280_ = stack[3].m_obj;
lean_object* v___y_281_ = stack[4].m_obj;
lean_object* v___y_282_ = stack[5].m_obj;
lean_object* v___y_283_ = stack[6].m_obj;
lean_object* v___y_284_ = stack[7].m_obj;
lean_object* v___y_285_ = stack[8].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(lean_box(0), v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___boxed(lean_object* v_00_u03b1_289_, lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(v_00_u03b1_289_, v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_299_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1(){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_313_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1));
v___x_315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3));
v___x_316_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoBreak___boxed), 10, 0);
v___x_317_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_313_, v___x_314_, v___x_315_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_318_;
v_res_318_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___boxed(lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
return v_res_320_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoContinue___redArg___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_Elab_Do_elabDoContinue___redArg___closed__0));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
lean_object* l_Lean_Elab_Do_elabDoContinue___redArg(lean_object* v_dec_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_325_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
if (lean_obj_tag(v_a_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_336_; 
v_val_335_ = lean_ctor_get(v_a_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v_a_334_, 1);
v___x_336_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(v_dec_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; 
lean_dec_ref_known(v___x_336_, 1);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc_ref(v_a_325_);
v___x_337_ = lean_apply_8(v_val_335_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, lean_box(0));
return v___x_337_;
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_val_335_);
v_a_338_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_336_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_336_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_a_334_);
lean_dec_ref(v_dec_324_);
v___x_346_ = lean_obj_once(&l_Lean_Elab_Do_elabDoContinue___redArg___closed__1, &l_Lean_Elab_Do_elabDoContinue___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoContinue___redArg___closed__1);
v___x_347_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(v___x_346_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
return v___x_347_;
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_dec_324_);
v_a_348_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_333_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_333_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoContinue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_dec_324_ = stack[0].m_obj;
lean_object* v_a_325_ = stack[1].m_obj;
lean_object* v_a_326_ = stack[2].m_obj;
lean_object* v_a_327_ = stack[3].m_obj;
lean_object* v_a_328_ = stack[4].m_obj;
lean_object* v_a_329_ = stack[5].m_obj;
lean_object* v_a_330_ = stack[6].m_obj;
lean_object* v_a_331_ = stack[7].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_Elab_Do_elabDoContinue___redArg(v_dec_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___redArg___boxed(lean_object* v_dec_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_Do_elabDoContinue___redArg(v_dec_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_366_;
}
}
lean_object* l_Lean_Elab_Do_elabDoContinue(lean_object* v___stx_367_, lean_object* v_dec_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_Do_elabDoContinue___redArg(v_dec_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoContinue_0interp(lean_interpreter_value* stack)
{
lean_object* v___stx_367_ = stack[0].m_obj;
lean_object* v_dec_368_ = stack[1].m_obj;
lean_object* v_a_369_ = stack[2].m_obj;
lean_object* v_a_370_ = stack[3].m_obj;
lean_object* v_a_371_ = stack[4].m_obj;
lean_object* v_a_372_ = stack[5].m_obj;
lean_object* v_a_373_ = stack[6].m_obj;
lean_object* v_a_374_ = stack[7].m_obj;
lean_object* v_a_375_ = stack[8].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Elab_Do_elabDoContinue(v___stx_367_, v_dec_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoContinue___boxed(lean_object* v___stx_379_, lean_object* v_dec_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Elab_Do_elabDoContinue(v___stx_379_, v_dec_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v___stx_379_);
return v_res_389_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1(){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_403_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_404_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1));
v___x_405_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3));
v___x_406_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoContinue___boxed), 10, 0);
v___x_407_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_403_, v___x_404_, v___x_405_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_408_;
v_res_408_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___boxed(lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
return v_res_410_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Jump(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Jump(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_BuiltinDo_Jump(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Jump(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Jump(builtin);
}
#ifdef __cplusplus
}
#endif
