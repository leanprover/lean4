// Lean compiler output
// Module: Lean.Elab.Tactic.Repeat
// Imports: public import Lean.Meta.Tactic.Repeat public import Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_to_list(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticRepeat_"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 101, 42, 245, 144, 172, 68, 230)}};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRepeat"};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 2, 135, 3, 239, 19, 147, 235)}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat'"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat_x27___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 67, 182, 138, 186, 187, 207, 59)}};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat_x27___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalRepeat'"};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 65, 105, 73, 181, 112, 150, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value),((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`repeat1'` made no progress"};
static const lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "repeat1'"};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 218, 230, 6, 131, 194, 196, 129)}};
static const lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalRepeat1'"};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 244, 156, 48, 248, 22, 45, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0(void){
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v___y_18_ = stack[8].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_32_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(lean_object* v___x_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_box(0);
v___x_44_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_35_, v___y_37_, v___y_39_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_44_, 1);
lean_inc(v___x_33_);
v___x_46_ = l_Lean_Elab_Tactic_evalTactic(v___x_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_dec_ref_known(v___x_46_, 1);
lean_dec(v_a_45_);
goto _start;
}
else
{
lean_object* v_a_48_; uint8_t v___y_50_; uint8_t v___x_60_; 
lean_dec(v___x_33_);
v_a_48_ = lean_ctor_get(v___x_46_, 0);
v___x_60_ = l_Lean_Exception_isInterrupt(v_a_48_);
if (v___x_60_ == 0)
{
uint8_t v___x_61_; 
lean_inc(v_a_48_);
v___x_61_ = l_Lean_Exception_isRuntime(v_a_48_);
v___y_50_ = v___x_61_;
goto v___jp_49_;
}
else
{
v___y_50_ = v___x_60_;
goto v___jp_49_;
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec_ref_known(v___x_46_, 1);
v___x_51_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_45_, v___y_50_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; 
v_unused_59_ = lean_ctor_get(v___x_51_, 0);
lean_dec(v_unused_59_);
v___x_53_ = v___x_51_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_dec(v___x_51_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_43_);
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_43_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
else
{
return v___x_51_;
}
}
else
{
lean_dec(v_a_45_);
return v___x_46_;
}
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec(v___x_33_);
v_a_62_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_44_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_44_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_33_ = stack[0].m_obj;
lean_object* v___y_34_ = stack[1].m_obj;
lean_object* v___y_35_ = stack[2].m_obj;
lean_object* v___y_36_ = stack[3].m_obj;
lean_object* v___y_37_ = stack[4].m_obj;
lean_object* v___y_38_ = stack[5].m_obj;
lean_object* v___y_39_ = stack[6].m_obj;
lean_object* v___y_40_ = stack[7].m_obj;
lean_object* v___y_41_ = stack[8].m_obj;
lean_object* v_res_70_;
v_res_70_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg___boxed(lean_object* v___x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0(lean_object* v___x_82_, lean_object* v___x_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_82_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_93_, 0);
lean_dec(v_unused_101_);
v___x_95_ = v___x_93_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_dec(v___x_93_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_83_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_83_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
return v___x_93_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRepeat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_82_ = stack[0].m_obj;
lean_object* v___x_83_ = stack[1].m_obj;
lean_object* v___y_84_ = stack[2].m_obj;
lean_object* v___y_85_ = stack[3].m_obj;
lean_object* v___y_86_ = stack[4].m_obj;
lean_object* v___y_87_ = stack[5].m_obj;
lean_object* v___y_88_ = stack[6].m_obj;
lean_object* v___y_89_ = stack[7].m_obj;
lean_object* v___y_90_ = stack[8].m_obj;
lean_object* v___y_91_ = stack[9].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_Elab_Tactic_evalRepeat___lam__0(v___x_82_, v___x_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed(lean_object* v___x_103_, lean_object* v___x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Elab_Tactic_evalRepeat___lam__0(v___x_103_, v___x_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_114_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRepeat(lean_object* v_stx_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__4));
lean_inc(v_stx_130_);
v___x_141_ = l_Lean_Syntax_isOfKind(v_stx_130_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec(v_stx_130_);
v___x_142_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = l_Lean_Syntax_getArg(v_stx_130_, v___x_143_);
lean_dec(v_stx_130_);
v___x_145_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_144_);
v___x_146_ = l_Lean_Syntax_isOfKind(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
lean_dec(v___x_144_);
v___x_147_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed), 11, 2);
lean_closure_set(v___f_149_, 0, v___x_144_);
lean_closure_set(v___f_149_, 1, v___x_148_);
v___x_150_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_149_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRepeat_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_130_ = stack[0].m_obj;
lean_object* v_a_131_ = stack[1].m_obj;
lean_object* v_a_132_ = stack[2].m_obj;
lean_object* v_a_133_ = stack[3].m_obj;
lean_object* v_a_134_ = stack[4].m_obj;
lean_object* v_a_135_ = stack[5].m_obj;
lean_object* v_a_136_ = stack[6].m_obj;
lean_object* v_a_137_ = stack[7].m_obj;
lean_object* v_a_138_ = stack[8].m_obj;
lean_object* v_res_151_;
v_res_151_ = l_Lean_Elab_Tactic_evalRepeat(v_stx_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___boxed(lean_object* v_stx_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Elab_Tactic_evalRepeat(v_stx_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_162_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(lean_object* v___x_163_, lean_object* v_inst_164_, lean_object* v_a_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_163_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
return v___x_175_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_163_ = stack[0].m_obj;
lean_object* v_a_165_ = stack[2].m_obj;
lean_object* v___y_166_ = stack[3].m_obj;
lean_object* v___y_167_ = stack[4].m_obj;
lean_object* v___y_168_ = stack[5].m_obj;
lean_object* v___y_169_ = stack[6].m_obj;
lean_object* v___y_170_ = stack[7].m_obj;
lean_object* v___y_171_ = stack[8].m_obj;
lean_object* v___y_172_ = stack[9].m_obj;
lean_object* v___y_173_ = stack[10].m_obj;
lean_object* v_res_176_;
v_res_176_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(v___x_163_, lean_box(0), v_a_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(lean_object* v___x_177_, lean_object* v_inst_178_, lean_object* v_a_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(v___x_177_, v_inst_178_, v_a_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_189_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1(){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_199_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__4));
v___x_200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2));
v___x_201_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat___boxed), 10, 0);
v___x_202_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_198_, v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_203_;
v_res_203_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___boxed(lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
return v_res_205_;
}
}
lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_208_, v___y_210_, v___y_212_, v___y_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_208_, v___y_210_, v___y_212_, v___y_214_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
v___x_220_ = lean_apply_9(v_x_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_a_219_);
lean_dec(v_a_217_);
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_a_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_268_; 
v_a_230_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_268_ == 0)
{
v___x_232_ = v___x_220_;
v_isShared_233_ = v_isSharedCheck_268_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_220_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_268_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___y_235_; uint8_t v___x_266_; 
v___x_266_ = l_Lean_Exception_isInterrupt(v_a_230_);
if (v___x_266_ == 0)
{
uint8_t v___x_267_; 
lean_inc(v_a_230_);
v___x_267_ = l_Lean_Exception_isRuntime(v_a_230_);
v___y_235_ = v___x_267_;
goto v___jp_234_;
}
else
{
v___y_235_ = v___x_266_;
goto v___jp_234_;
}
v___jp_234_:
{
if (v___y_235_ == 0)
{
lean_object* v___x_236_; 
lean_del_object(v___x_232_);
lean_dec(v_a_230_);
v___x_236_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_219_, v___y_235_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
lean_dec_ref_known(v___x_236_, 1);
v___x_237_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_217_, v___y_235_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_246_);
v___x_239_ = v___x_237_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_dec(v___x_237_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_237_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_237_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_a_217_);
v_a_255_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_236_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_236_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_a_219_);
lean_dec(v_a_217_);
if (v_isShared_233_ == 0)
{
v___x_264_ = v___x_232_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_230_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_217_);
lean_dec_ref(v_x_206_);
v_a_269_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_218_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_218_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec_ref(v_x_206_);
v_a_277_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_216_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_216_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_206_ = stack[0].m_obj;
lean_object* v___y_207_ = stack[1].m_obj;
lean_object* v___y_208_ = stack[2].m_obj;
lean_object* v___y_209_ = stack[3].m_obj;
lean_object* v___y_210_ = stack[4].m_obj;
lean_object* v___y_211_ = stack[5].m_obj;
lean_object* v___y_212_ = stack[6].m_obj;
lean_object* v___y_213_ = stack[7].m_obj;
lean_object* v___y_214_ = stack[8].m_obj;
lean_object* v_res_285_;
v_res_285_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_296_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(lean_object* v_keys_297_, lean_object* v_i_298_, lean_object* v_k_299_){
_start:
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_array_get_size(v_keys_297_);
v___x_301_ = lean_nat_dec_lt(v_i_298_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v_i_298_);
return v___x_301_;
}
else
{
lean_object* v_k_x27_302_; uint8_t v___x_303_; 
v_k_x27_302_ = lean_array_fget_borrowed(v_keys_297_, v_i_298_);
v___x_303_ = l_Lean_instBEqMVarId_beq(v_k_299_, v_k_x27_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_i_298_, v___x_304_);
lean_dec(v_i_298_);
v_i_298_ = v___x_305_;
goto _start;
}
else
{
lean_dec(v_i_298_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_297_ = stack[0].m_obj;
lean_object* v_i_298_ = stack[1].m_obj;
lean_object* v_k_299_ = stack[2].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_297_, v_i_298_, v_k_299_);
stack->m_num = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_keys_308_, lean_object* v_i_309_, lean_object* v_k_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_308_, v_i_309_, v_k_310_);
lean_dec(v_k_310_);
lean_dec_ref(v_keys_308_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(lean_object* v_x_313_, size_t v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v_es_316_; lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v_j_320_; lean_object* v___x_321_; 
v_es_316_ = lean_ctor_get(v_x_313_, 0);
v___x_317_ = lean_box(2);
v___x_318_ = ((size_t)31ULL);
v___x_319_ = lean_usize_land(v_x_314_, v___x_318_);
v_j_320_ = lean_usize_to_nat(v___x_319_);
v___x_321_ = lean_array_get_borrowed(v___x_317_, v_es_316_, v_j_320_);
lean_dec(v_j_320_);
switch(lean_obj_tag(v___x_321_))
{
case 0:
{
lean_object* v_key_322_; uint8_t v___x_323_; 
v_key_322_ = lean_ctor_get(v___x_321_, 0);
v___x_323_ = l_Lean_instBEqMVarId_beq(v_x_315_, v_key_322_);
return v___x_323_;
}
case 1:
{
lean_object* v_node_324_; size_t v___x_325_; size_t v___x_326_; 
v_node_324_ = lean_ctor_get(v___x_321_, 0);
v___x_325_ = ((size_t)5ULL);
v___x_326_ = lean_usize_shift_right(v_x_314_, v___x_325_);
v_x_313_ = v_node_324_;
v_x_314_ = v___x_326_;
goto _start;
}
default: 
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
}
}
else
{
lean_object* v_ks_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_ks_329_ = lean_ctor_get(v_x_313_, 0);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_ks_329_, v___x_330_, v_x_315_);
return v___x_331_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_313_ = stack[0].m_obj;
size_t v_x_314_ = stack[1].m_num;
lean_object* v_x_315_ = stack[2].m_obj;
uint8_t v_res_332_;
v_res_332_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_313_, v_x_314_, v_x_315_);
stack->m_num = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
size_t v_x_4481__boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_x_4481__boxed_336_ = lean_unbox_usize(v_x_334_);
lean_dec(v_x_334_);
v_res_337_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_333_, v_x_4481__boxed_336_, v_x_335_);
lean_dec(v_x_335_);
lean_dec_ref(v_x_333_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
uint64_t v___x_341_; size_t v___x_342_; uint8_t v___x_343_; 
v___x_341_ = l_Lean_instHashableMVarId_hash(v_x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_339_, v___x_342_, v_x_340_);
return v___x_343_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_339_ = stack[0].m_obj;
lean_object* v_x_340_ = stack[1].m_obj;
uint8_t v_res_344_;
v_res_344_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_339_, v_x_340_);
stack->m_num = v_res_344_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_345_, v_x_346_);
lean_dec(v_x_346_);
lean_dec_ref(v_x_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v_mctx_353_; lean_object* v_eAssignment_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_352_ = lean_st_ref_get(v___y_350_);
v_mctx_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_mctx_353_);
lean_dec(v___x_352_);
v_eAssignment_354_ = lean_ctor_get(v_mctx_353_, 8);
lean_inc_ref(v_eAssignment_354_);
lean_dec_ref(v_mctx_353_);
v___x_355_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_eAssignment_354_, v_mvarId_349_);
lean_dec_ref(v_eAssignment_354_);
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_349_ = stack[0].m_obj;
lean_object* v___y_350_ = stack[1].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_349_, v___y_350_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec(v_mvarId_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
return v_x_363_;
}
else
{
lean_object* v_head_365_; lean_object* v_tail_366_; lean_object* v___x_367_; 
v_head_365_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_head_365_);
v_tail_366_ = lean_ctor_get(v_x_364_, 1);
lean_inc(v_tail_366_);
lean_dec_ref_known(v_x_364_, 2);
v___x_367_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_363_, v_head_365_);
v_x_363_ = v___x_367_;
v_x_364_ = v_tail_366_;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(lean_object* v_f_369_, lean_object* v_a_370_, uint8_t v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
if (lean_obj_tag(v_a_372_) == 0)
{
if (lean_obj_tag(v_a_373_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_a_370_);
lean_dec_ref(v_f_369_);
v___x_384_ = lean_box(v_a_371_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_a_374_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_head_387_; lean_object* v_tail_388_; 
v_head_387_ = lean_ctor_get(v_a_373_, 0);
lean_inc(v_head_387_);
v_tail_388_ = lean_ctor_get(v_a_373_, 1);
lean_inc(v_tail_388_);
lean_dec_ref_known(v_a_373_, 2);
v_a_372_ = v_head_387_;
v_a_373_ = v_tail_388_;
goto _start;
}
}
else
{
lean_object* v_head_390_; lean_object* v_tail_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_434_; 
v_head_390_ = lean_ctor_get(v_a_372_, 0);
v_tail_391_ = lean_ctor_get(v_a_372_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_372_);
if (v_isSharedCheck_434_ == 0)
{
v___x_393_ = v_a_372_;
v_isShared_394_ = v_isSharedCheck_434_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_tail_391_);
lean_inc(v_head_390_);
lean_dec(v_a_372_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_434_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_433_; 
v___x_395_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_head_390_, v___y_380_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_433_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_433_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_433_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = lean_unbox(v_a_396_);
lean_dec(v_a_396_);
if (v___x_400_ == 0)
{
lean_object* v_zero_401_; uint8_t v_isZero_402_; 
v_zero_401_ = lean_unsigned_to_nat(0u);
v_isZero_402_ = lean_nat_dec_eq(v_a_370_, v_zero_401_);
if (v_isZero_402_ == 1)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
lean_del_object(v___x_393_);
lean_dec(v_a_370_);
lean_dec_ref(v_f_369_);
v___x_403_ = lean_array_push(v_a_374_, v_head_390_);
v___x_404_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_403_, v_tail_391_);
v___x_405_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(v___x_404_, v_a_373_);
v___x_406_ = lean_box(v_a_371_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_407_);
v___x_409_ = v___x_398_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v_one_411_; lean_object* v_n_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_del_object(v___x_398_);
v_one_411_ = lean_unsigned_to_nat(1u);
v_n_412_ = lean_nat_sub(v_a_370_, v_one_411_);
lean_dec(v_a_370_);
v___x_413_ = 1;
lean_inc_ref(v_f_369_);
lean_inc(v_head_390_);
v___x_414_ = lean_apply_1(v_f_369_, v_head_390_);
v___x_415_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v___x_414_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
if (lean_obj_tag(v_a_416_) == 0)
{
lean_object* v___x_417_; 
lean_del_object(v___x_393_);
v___x_417_ = lean_array_push(v_a_374_, v_head_390_);
v_a_370_ = v_n_412_;
v_a_372_ = v_tail_391_;
v_a_374_ = v___x_417_;
goto _start;
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; 
lean_dec(v_head_390_);
v_val_419_ = lean_ctor_get(v_a_416_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_a_416_, 1);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_a_373_);
lean_ctor_set(v___x_393_, 0, v_tail_391_);
v___x_421_ = v___x_393_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_tail_391_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_a_373_);
v___x_421_ = v_reuseFailAlloc_423_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_a_370_ = v_n_412_;
v_a_371_ = v___x_413_;
v_a_372_ = v_val_419_;
v_a_373_ = v___x_421_;
goto _start;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_n_412_);
lean_del_object(v___x_393_);
lean_dec(v_tail_391_);
lean_dec(v_head_390_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_f_369_);
v_a_424_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_415_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_415_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_del_object(v___x_398_);
lean_del_object(v___x_393_);
lean_dec(v_head_390_);
v_a_372_ = v_tail_391_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_369_ = stack[0].m_obj;
lean_object* v_a_370_ = stack[1].m_obj;
uint8_t v_a_371_ = stack[2].m_num;
lean_object* v_a_372_ = stack[3].m_obj;
lean_object* v_a_373_ = stack[4].m_obj;
lean_object* v_a_374_ = stack[5].m_obj;
lean_object* v___y_375_ = stack[6].m_obj;
lean_object* v___y_376_ = stack[7].m_obj;
lean_object* v___y_377_ = stack[8].m_obj;
lean_object* v___y_378_ = stack[9].m_obj;
lean_object* v___y_379_ = stack[10].m_obj;
lean_object* v___y_380_ = stack[11].m_obj;
lean_object* v___y_381_ = stack[12].m_obj;
lean_object* v___y_382_ = stack[13].m_obj;
lean_object* v_res_435_;
v_res_435_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_f_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v_a_4602__boxed_451_; lean_object* v_res_452_; 
v_a_4602__boxed_451_ = lean_unbox(v_a_438_);
v_res_452_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_436_, v_a_437_, v_a_4602__boxed_451_, v_a_439_, v_a_440_, v_a_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_452_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(lean_object* v_as_453_, size_t v_i_454_, size_t v_stop_455_, lean_object* v_b_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_a_467_; uint8_t v___x_471_; 
v___x_471_ = lean_usize_dec_eq(v_i_454_, v_stop_455_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_475_; 
v___x_472_ = lean_array_uget_borrowed(v_as_453_, v_i_454_);
v___x_475_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v___x_472_, v___y_462_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; uint8_t v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = lean_unbox(v_a_476_);
lean_dec(v_a_476_);
if (v___x_477_ == 0)
{
goto v___jp_473_;
}
else
{
v_a_467_ = v_b_456_;
goto v___jp_466_;
}
}
else
{
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_478_; uint8_t v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_475_, 1);
v___x_479_ = lean_unbox(v_a_478_);
lean_dec(v_a_478_);
if (v___x_479_ == 0)
{
v_a_467_ = v_b_456_;
goto v___jp_466_;
}
else
{
goto v___jp_473_;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_b_456_);
v_a_480_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_475_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_475_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
v___jp_473_:
{
lean_object* v___x_474_; 
lean_inc(v___x_472_);
v___x_474_ = lean_array_push(v_b_456_, v___x_472_);
v_a_467_ = v___x_474_;
goto v___jp_466_;
}
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_b_456_);
return v___x_488_;
}
v___jp_466_:
{
size_t v___x_468_; size_t v___x_469_; 
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_add(v_i_454_, v___x_468_);
v_i_454_ = v___x_469_;
v_b_456_ = v_a_467_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_453_ = stack[0].m_obj;
size_t v_i_454_ = stack[1].m_num;
size_t v_stop_455_ = stack[2].m_num;
lean_object* v_b_456_ = stack[3].m_obj;
lean_object* v___y_457_ = stack[4].m_obj;
lean_object* v___y_458_ = stack[5].m_obj;
lean_object* v___y_459_ = stack[6].m_obj;
lean_object* v___y_460_ = stack[7].m_obj;
lean_object* v___y_461_ = stack[8].m_obj;
lean_object* v___y_462_ = stack[9].m_obj;
lean_object* v___y_463_ = stack[10].m_obj;
lean_object* v___y_464_ = stack[11].m_obj;
lean_object* v_res_489_;
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_453_, v_i_454_, v_stop_455_, v_b_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(lean_object* v_as_490_, lean_object* v_i_491_, lean_object* v_stop_492_, lean_object* v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_i_boxed_503_; size_t v_stop_boxed_504_; lean_object* v_res_505_; 
v_i_boxed_503_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_504_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_490_, v_i_boxed_503_, v_stop_boxed_504_, v_b_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec_ref(v_as_490_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0));
v___x_509_ = lean_array_to_list(v___x_508_);
return v___x_509_;
}
}
lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(lean_object* v_f_510_, lean_object* v_goals_511_, lean_object* v_maxIters_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = 0;
v___x_523_ = lean_box(0);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0));
v___x_526_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_510_, v_maxIters_512_, v___x_522_, v_goals_511_, v___x_523_, v___x_525_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_569_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_569_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_569_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_569_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_568_; 
v_fst_531_ = lean_ctor_get(v_a_527_, 0);
v_snd_532_ = lean_ctor_get(v_a_527_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_527_);
if (v_isSharedCheck_568_ == 0)
{
v___x_534_ = v_a_527_;
v_isShared_535_ = v_isSharedCheck_568_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snd_532_);
lean_inc(v_fst_531_);
lean_dec(v_a_527_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_568_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_array_get_size(v_snd_532_);
v___x_537_ = lean_nat_dec_lt(v___x_524_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_dec(v_snd_532_);
v___x_538_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_538_);
v___x_540_ = v___x_534_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_fst_531_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_540_);
v___x_542_ = v___x_529_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; 
lean_del_object(v___x_529_);
v___x_545_ = ((size_t)0ULL);
v___x_546_ = lean_usize_of_nat(v___x_536_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_532_, v___x_545_, v___x_546_, v___x_525_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v_snd_532_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_559_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_array_to_list(v_a_548_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_552_);
v___x_554_ = v___x_534_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_fst_531_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_del_object(v___x_534_);
lean_dec(v_fst_531_);
v_a_560_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_547_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_547_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_a_570_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_526_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_526_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_510_ = stack[0].m_obj;
lean_object* v_goals_511_ = stack[1].m_obj;
lean_object* v_maxIters_512_ = stack[2].m_obj;
lean_object* v___y_513_ = stack[3].m_obj;
lean_object* v___y_514_ = stack[4].m_obj;
lean_object* v___y_515_ = stack[5].m_obj;
lean_object* v___y_516_ = stack[6].m_obj;
lean_object* v___y_517_ = stack[7].m_obj;
lean_object* v___y_518_ = stack[8].m_obj;
lean_object* v___y_519_ = stack[9].m_obj;
lean_object* v___y_520_ = stack[10].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_510_, v_goals_511_, v_maxIters_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed(lean_object* v_f_579_, lean_object* v_goals_580_, lean_object* v_maxIters_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_579_, v_goals_580_, v_maxIters_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(lean_object* v_x_592_){
_start:
{
lean_object* v_snd_593_; 
v_snd_593_ = lean_ctor_get(v_x_592_, 1);
lean_inc(v_snd_593_);
return v_snd_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(v_x_594_);
lean_dec_ref(v_x_594_);
return v_res_595_;
}
}
lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(lean_object* v_a_596_, lean_object* v_f_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
lean_inc(v___y_605_);
lean_inc_ref(v___y_604_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
v___x_607_ = lean_apply_9(v_a_596_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, lean_box(0));
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_616_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_apply_1(v_f_597_, v_a_608_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_f_597_);
v_a_617_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_607_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_607_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT void l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_596_ = stack[0].m_obj;
lean_object* v_f_597_ = stack[1].m_obj;
lean_object* v___y_598_ = stack[2].m_obj;
lean_object* v___y_599_ = stack[3].m_obj;
lean_object* v___y_600_ = stack[4].m_obj;
lean_object* v___y_601_ = stack[5].m_obj;
lean_object* v___y_602_ = stack[6].m_obj;
lean_object* v___y_603_ = stack[7].m_obj;
lean_object* v___y_604_ = stack[8].m_obj;
lean_object* v___y_605_ = stack[9].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_596_, v_f_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg___boxed(lean_object* v_a_626_, lean_object* v_f_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_626_, v_f_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_637_;
}
}
lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(lean_object* v_f_639_, lean_object* v_goals_640_, lean_object* v_maxIters_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___f_651_ = ((lean_object*)(l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0));
v___x_652_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed), 12, 3);
lean_closure_set(v___x_652_, 0, v_f_639_);
lean_closure_set(v___x_652_, 1, v_goals_640_);
lean_closure_set(v___x_652_, 2, v_maxIters_641_);
v___x_653_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v___x_652_, v___f_651_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v___x_653_;
}
}
LEAN_EXPORT void l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_639_ = stack[0].m_obj;
lean_object* v_goals_640_ = stack[1].m_obj;
lean_object* v_maxIters_641_ = stack[2].m_obj;
lean_object* v___y_642_ = stack[3].m_obj;
lean_object* v___y_643_ = stack[4].m_obj;
lean_object* v___y_644_ = stack[5].m_obj;
lean_object* v___y_645_ = stack[6].m_obj;
lean_object* v___y_646_ = stack[7].m_obj;
lean_object* v___y_647_ = stack[8].m_obj;
lean_object* v___y_648_ = stack[9].m_obj;
lean_object* v___y_649_ = stack[10].m_obj;
lean_object* v_res_654_;
v_res_654_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v_f_639_, v_goals_640_, v_maxIters_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_654_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(lean_object* v_f_655_, lean_object* v_goals_656_, lean_object* v_maxIters_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v_f_655_, v_goals_656_, v_maxIters_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_667_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRepeat_x27(lean_object* v_stx_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1));
lean_inc(v_stx_674_);
v___x_685_ = l_Lean_Syntax_isOfKind(v_stx_674_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
lean_dec(v_stx_674_);
v___x_686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = l_Lean_Syntax_getArg(v_stx_674_, v___x_687_);
lean_dec(v_stx_674_);
v___x_689_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_688_);
v___x_690_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
lean_dec(v___x_688_);
v___x_691_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_691_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_676_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw___boxed), 11, 1);
lean_closure_set(v___x_694_, 0, v___x_688_);
v___x_695_ = lean_unsigned_to_nat(100000u);
v___x_696_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v___x_694_, v_a_693_, v___x_695_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_697_, v_a_676_);
return v___x_698_;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_696_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_696_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v___x_688_);
v_a_707_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_692_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_692_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRepeat_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_674_ = stack[0].m_obj;
lean_object* v_a_675_ = stack[1].m_obj;
lean_object* v_a_676_ = stack[2].m_obj;
lean_object* v_a_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_a_680_ = stack[6].m_obj;
lean_object* v_a_681_ = stack[7].m_obj;
lean_object* v_a_682_ = stack[8].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_Elab_Tactic_evalRepeat_x27(v_stx_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27___boxed(lean_object* v_stx_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Elab_Tactic_evalRepeat_x27(v_stx_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_726_;
}
}
lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_a_729_, lean_object* v_f_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_729_, v_f_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT void l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_729_ = stack[2].m_obj;
lean_object* v_f_730_ = stack[3].m_obj;
lean_object* v___y_731_ = stack[4].m_obj;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v___y_733_ = stack[6].m_obj;
lean_object* v___y_734_ = stack[7].m_obj;
lean_object* v___y_735_ = stack[8].m_obj;
lean_object* v___y_736_ = stack[9].m_obj;
lean_object* v___y_737_ = stack[10].m_obj;
lean_object* v___y_738_ = stack[11].m_obj;
lean_object* v_res_741_;
v_res_741_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(lean_box(0), lean_box(0), v_a_729_, v_f_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_a_744_, lean_object* v_f_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(v_00_u03b1_742_, v_00_u03b2_743_, v_a_744_, v_f_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_755_;
}
}
lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_756_, lean_object* v_x_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_757_ = stack[1].m_obj;
lean_object* v___y_758_ = stack[2].m_obj;
lean_object* v___y_759_ = stack[3].m_obj;
lean_object* v___y_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v___y_762_ = stack[6].m_obj;
lean_object* v___y_763_ = stack[7].m_obj;
lean_object* v___y_764_ = stack[8].m_obj;
lean_object* v___y_765_ = stack[9].m_obj;
lean_object* v_res_768_;
v_res_768_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(lean_box(0), v_x_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_780_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(lean_object* v_mvarId_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_781_, v___y_787_);
return v___x_791_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_781_ = stack[0].m_obj;
lean_object* v___y_782_ = stack[1].m_obj;
lean_object* v___y_783_ = stack[2].m_obj;
lean_object* v___y_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v___y_786_ = stack[5].m_obj;
lean_object* v___y_787_ = stack[6].m_obj;
lean_object* v___y_788_ = stack[7].m_obj;
lean_object* v___y_789_ = stack[8].m_obj;
lean_object* v_res_792_;
v_res_792_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_mvarId_793_);
return v_res_803_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_805_ = stack[1].m_obj;
lean_object* v_x_806_ = stack[2].m_obj;
uint8_t v_res_808_;
v_res_808_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(lean_box(0), v_x_805_, v_x_806_);
stack->m_num = v_res_808_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_809_, v_x_810_, v_x_811_);
lean_dec(v_x_811_);
lean_dec_ref(v_x_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, size_t v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_815_, v_x_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_815_ = stack[1].m_obj;
size_t v_x_816_ = stack[2].m_num;
lean_object* v_x_817_ = stack[3].m_obj;
uint8_t v_res_819_;
v_res_819_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(lean_box(0), v_x_815_, v_x_816_, v_x_817_);
stack->m_num = v_res_819_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
size_t v_x_5610__boxed_824_; uint8_t v_res_825_; lean_object* v_r_826_; 
v_x_5610__boxed_824_ = lean_unbox_usize(v_x_822_);
lean_dec(v_x_822_);
v_res_825_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_820_, v_x_821_, v_x_5610__boxed_824_, v_x_823_);
lean_dec(v_x_823_);
lean_dec_ref(v_x_821_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_k_832_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_828_, v_i_831_, v_k_832_);
return v___x_833_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_828_ = stack[1].m_obj;
lean_object* v_vals_829_ = stack[2].m_obj;
lean_object* v_i_831_ = stack[4].m_obj;
lean_object* v_k_832_ = stack[5].m_obj;
uint8_t v_res_834_;
v_res_834_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_box(0), v_keys_828_, v_vals_829_, lean_box(0), v_i_831_, v_k_832_);
stack->m_num = v_res_834_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_k_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(v_00_u03b2_835_, v_keys_836_, v_vals_837_, v_heq_838_, v_i_839_, v_k_840_);
lean_dec(v_k_840_);
lean_dec_ref(v_vals_837_);
lean_dec_ref(v_keys_836_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1(){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_850_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_851_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1));
v___x_852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1));
v___x_853_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat_x27___boxed), 10, 0);
v___x_854_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_850_, v___x_851_, v___x_852_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_855_;
v_res_855_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___boxed(lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
return v_res_857_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3(){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1));
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6));
v___x_886_ = l_Lean_addBuiltinDeclarationRanges(v___x_884_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_887_;
v_res_887_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
return v_res_889_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(lean_object* v_msgData_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; lean_object* v_env_897_; uint8_t v___x_898_; lean_object* v_env_899_; lean_object* v___x_900_; lean_object* v_toCold_901_; lean_object* v_mctx_902_; lean_object* v_lctx_903_; lean_object* v_options_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_896_ = lean_st_ref_get(v___y_894_);
v_env_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_ref(v_env_897_);
lean_dec(v___x_896_);
v___x_898_ = 0;
v_env_899_ = l_Lean_Environment_setRecordingDeps(v_env_897_, v___x_898_);
v___x_900_ = lean_st_ref_get(v___y_892_);
v_toCold_901_ = lean_ctor_get(v___y_893_, 0);
v_mctx_902_ = lean_ctor_get(v___x_900_, 0);
lean_inc_ref(v_mctx_902_);
lean_dec(v___x_900_);
v_lctx_903_ = lean_ctor_get(v___y_891_, 2);
v_options_904_ = lean_ctor_get(v_toCold_901_, 2);
lean_inc_ref(v_options_904_);
lean_inc_ref(v_lctx_903_);
v___x_905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_905_, 0, v_env_899_);
lean_ctor_set(v___x_905_, 1, v_mctx_902_);
lean_ctor_set(v___x_905_, 2, v_lctx_903_);
lean_ctor_set(v___x_905_, 3, v_options_904_);
v___x_906_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v_msgData_890_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_890_ = stack[0].m_obj;
lean_object* v___y_891_ = stack[1].m_obj;
lean_object* v___y_892_ = stack[2].m_obj;
lean_object* v___y_893_ = stack[3].m_obj;
lean_object* v___y_894_ = stack[4].m_obj;
lean_object* v_res_908_;
v_res_908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(lean_object* v_msg_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_ref_922_ = lean_ctor_get(v___y_919_, 2);
v___x_923_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msg_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_932_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
lean_inc(v_ref_922_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_ref_922_);
lean_ctor_set(v___x_928_, 1, v_a_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 1);
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_916_ = stack[0].m_obj;
lean_object* v___y_917_ = stack[1].m_obj;
lean_object* v___y_918_ = stack[2].m_obj;
lean_object* v___y_919_ = stack[3].m_obj;
lean_object* v___y_920_ = stack[4].m_obj;
lean_object* v_res_933_;
v_res_933_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
stack->m_obj
 = v_res_933_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg___boxed(lean_object* v_msg_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(lean_object* v_f_944_, lean_object* v_goals_945_, lean_object* v_maxIters_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_944_, v_goals_945_, v_maxIters_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_969_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_969_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_969_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_969_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; uint8_t v___x_962_; 
v_fst_961_ = lean_ctor_get(v_a_957_, 0);
v___x_962_ = lean_unbox(v_fst_961_);
if (v___x_962_ == 1)
{
lean_object* v_snd_963_; lean_object* v___x_965_; 
v_snd_963_ = lean_ctor_get(v_a_957_, 1);
lean_inc(v_snd_963_);
lean_dec(v_a_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_snd_963_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_snd_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_959_);
lean_dec(v_a_957_);
v___x_967_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1);
v___x_968_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v___x_967_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
return v___x_968_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_956_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_956_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_944_ = stack[0].m_obj;
lean_object* v_goals_945_ = stack[1].m_obj;
lean_object* v_maxIters_946_ = stack[2].m_obj;
lean_object* v___y_947_ = stack[3].m_obj;
lean_object* v___y_948_ = stack[4].m_obj;
lean_object* v___y_949_ = stack[5].m_obj;
lean_object* v___y_950_ = stack[6].m_obj;
lean_object* v___y_951_ = stack[7].m_obj;
lean_object* v___y_952_ = stack[8].m_obj;
lean_object* v___y_953_ = stack[9].m_obj;
lean_object* v___y_954_ = stack[10].m_obj;
lean_object* v_res_978_;
v_res_978_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v_f_944_, v_goals_945_, v_maxIters_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___boxed(lean_object* v_f_979_, lean_object* v_goals_980_, lean_object* v_maxIters_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v_f_979_, v_goals_980_, v_maxIters_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_991_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27(lean_object* v_stx_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1));
lean_inc(v_stx_998_);
v___x_1009_ = l_Lean_Syntax_isOfKind(v_stx_998_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
lean_dec(v_stx_998_);
v___x_1010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = l_Lean_Syntax_getArg(v_stx_998_, v___x_1011_);
lean_dec(v_stx_998_);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_1012_);
v___x_1014_ = l_Lean_Syntax_isOfKind(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec(v___x_1012_);
v___x_1015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_1000_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw___boxed), 11, 1);
lean_closure_set(v___x_1018_, 0, v___x_1012_);
v___x_1019_ = lean_unsigned_to_nat(100000u);
v___x_1020_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v___x_1018_, v_a_1017_, v___x_1019_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_1021_, v_a_1000_);
return v___x_1022_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1020_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1020_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v___x_1012_);
v_a_1031_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1016_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1016_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRepeat1_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_998_ = stack[0].m_obj;
lean_object* v_a_999_ = stack[1].m_obj;
lean_object* v_a_1000_ = stack[2].m_obj;
lean_object* v_a_1001_ = stack[3].m_obj;
lean_object* v_a_1002_ = stack[4].m_obj;
lean_object* v_a_1003_ = stack[5].m_obj;
lean_object* v_a_1004_ = stack[6].m_obj;
lean_object* v_a_1005_ = stack[7].m_obj;
lean_object* v_a_1006_ = stack[8].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Lean_Elab_Tactic_evalRepeat1_x27(v_stx_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27___boxed(lean_object* v_stx_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Elab_Tactic_evalRepeat1_x27(v_stx_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1050_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(lean_object* v_00_u03b1_1051_, lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_1052_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1052_ = stack[1].m_obj;
lean_object* v___y_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v___y_1057_ = stack[6].m_obj;
lean_object* v___y_1058_ = stack[7].m_obj;
lean_object* v___y_1059_ = stack[8].m_obj;
lean_object* v___y_1060_ = stack[9].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(lean_box(0), v_msg_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(v_00_u03b1_1064_, v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1075_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1(){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1083_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1));
v___x_1085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1));
v___x_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat1_x27___boxed), 10, 0);
v___x_1087_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1083_, v___x_1084_, v___x_1085_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1088_;
v_res_1088_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___boxed(lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
return v_res_1090_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3(){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1));
v___x_1118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6));
v___x_1119_ = l_Lean_addBuiltinDeclarationRanges(v___x_1117_, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1120_;
v_res_1120_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
return v_res_1122_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Repeat(builtin);
}
#ifdef __cplusplus
}
#endif
