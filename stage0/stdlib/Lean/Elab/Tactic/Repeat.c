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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(lean_object* v___x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_33_, v___y_35_, v___y_37_, v___y_39_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_44_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
lean_inc(v___x_31_);
v___x_44_ = l_Lean_Elab_Tactic_evalTactic(v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_dec_ref_known(v___x_44_, 1);
lean_dec(v_a_43_);
goto _start;
}
else
{
lean_object* v_a_46_; uint8_t v___x_47_; 
lean_dec(v___x_31_);
v_a_46_ = lean_ctor_get(v___x_44_, 0);
v___x_47_ = l_Lean_Exception_isInterrupt(v_a_46_);
if (v___x_47_ == 0)
{
uint8_t v___x_48_; 
lean_inc(v_a_46_);
v___x_48_ = l_Lean_Exception_isRuntime(v_a_46_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec_ref_known(v___x_44_, 1);
v___x_49_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_43_, v___x_48_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v___x_49_, 0);
lean_dec(v_unused_57_);
v___x_51_ = v___x_49_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_dec(v___x_49_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_41_);
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_41_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
else
{
return v___x_49_;
}
}
else
{
lean_dec(v_a_43_);
return v___x_44_;
}
}
else
{
lean_dec(v_a_43_);
return v___x_44_;
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
lean_dec(v___x_31_);
v_a_58_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_42_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_42_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg___boxed(lean_object* v___x_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0(lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_77_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v___x_88_, 0);
lean_dec(v_unused_96_);
v___x_90_ = v___x_88_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_dec(v___x_88_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_78_);
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_78_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed(lean_object* v___x_97_, lean_object* v___x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Elab_Tactic_evalRepeat___lam__0(v___x_97_, v___x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat(lean_object* v_stx_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__4));
lean_inc(v_stx_124_);
v___x_135_ = l_Lean_Syntax_isOfKind(v_stx_124_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec(v_stx_124_);
v___x_136_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = l_Lean_Syntax_getArg(v_stx_124_, v___x_137_);
lean_dec(v_stx_124_);
v___x_139_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_138_);
v___x_140_ = l_Lean_Syntax_isOfKind(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_dec(v___x_138_);
v___x_141_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v___x_144_; 
v___x_142_ = lean_box(0);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed), 11, 2);
lean_closure_set(v___f_143_, 0, v___x_138_);
lean_closure_set(v___f_143_, 1, v___x_142_);
v___x_144_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_143_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___boxed(lean_object* v_stx_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Elab_Tactic_evalRepeat(v_stx_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(lean_object* v___x_156_, lean_object* v_inst_157_, lean_object* v_a_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_156_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(lean_object* v___x_169_, lean_object* v_inst_170_, lean_object* v_a_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(v___x_169_, v_inst_170_, v_a_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1(){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_190_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_191_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__4));
v___x_192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2));
v___x_193_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat___boxed), 10, 0);
v___x_194_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_190_, v___x_191_, v___x_192_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___boxed(lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_199_, v___y_201_, v___y_203_, v___y_205_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_199_, v___y_201_, v___y_203_, v___y_205_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
lean_inc(v___y_205_);
lean_inc_ref(v___y_204_);
lean_inc(v___y_203_);
lean_inc_ref(v___y_202_);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
lean_inc(v___y_199_);
lean_inc_ref(v___y_198_);
v___x_211_ = lean_apply_9(v_x_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, lean_box(0));
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_210_);
lean_dec(v_a_208_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_216_, 0, v_a_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_260_; 
v_a_221_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_260_ == 0)
{
v___x_223_ = v___x_211_;
v_isShared_224_ = v_isSharedCheck_260_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_260_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = l_Lean_Exception_isInterrupt(v_a_221_);
if (v___x_225_ == 0)
{
uint8_t v___x_226_; 
lean_inc(v_a_221_);
v___x_226_ = l_Lean_Exception_isRuntime(v_a_221_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_del_object(v___x_223_);
lean_dec(v_a_221_);
v___x_227_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_210_, v___x_226_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; 
lean_dec_ref_known(v___x_227_, 1);
v___x_228_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_208_, v___x_226_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_228_, 0);
lean_dec(v_unused_237_);
v___x_230_ = v___x_228_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_dec(v___x_228_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_box(0);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_228_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_228_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_a_208_);
v_a_246_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_227_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_227_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v___x_255_; 
lean_dec(v_a_210_);
lean_dec(v_a_208_);
if (v_isShared_224_ == 0)
{
v___x_255_ = v___x_223_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_221_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v_a_210_);
lean_dec(v_a_208_);
if (v_isShared_224_ == 0)
{
v___x_258_ = v___x_223_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_221_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_a_208_);
lean_dec_ref(v_x_197_);
v_a_261_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_209_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_209_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_x_197_);
v_a_269_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_207_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_207_);
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
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(lean_object* v_keys_288_, lean_object* v_i_289_, lean_object* v_k_290_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_keys_288_);
v___x_292_ = lean_nat_dec_lt(v_i_289_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec(v_i_289_);
return v___x_292_;
}
else
{
lean_object* v_k_x27_293_; uint8_t v___x_294_; 
v_k_x27_293_ = lean_array_fget_borrowed(v_keys_288_, v_i_289_);
v___x_294_ = l_Lean_instBEqMVarId_beq(v_k_290_, v_k_x27_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_i_289_, v___x_295_);
lean_dec(v_i_289_);
v_i_289_ = v___x_296_;
goto _start;
}
else
{
lean_dec(v_i_289_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_keys_298_, lean_object* v_i_299_, lean_object* v_k_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_298_, v_i_299_, v_k_300_);
lean_dec(v_k_300_);
lean_dec_ref(v_keys_298_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(lean_object* v_x_303_, size_t v_x_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_es_306_; lean_object* v___x_307_; size_t v___x_308_; size_t v___x_309_; lean_object* v_j_310_; lean_object* v___x_311_; 
v_es_306_ = lean_ctor_get(v_x_303_, 0);
v___x_307_ = lean_box(2);
v___x_308_ = ((size_t)31ULL);
v___x_309_ = lean_usize_land(v_x_304_, v___x_308_);
v_j_310_ = lean_usize_to_nat(v___x_309_);
v___x_311_ = lean_array_get_borrowed(v___x_307_, v_es_306_, v_j_310_);
lean_dec(v_j_310_);
switch(lean_obj_tag(v___x_311_))
{
case 0:
{
lean_object* v_key_312_; uint8_t v___x_313_; 
v_key_312_ = lean_ctor_get(v___x_311_, 0);
v___x_313_ = l_Lean_instBEqMVarId_beq(v_x_305_, v_key_312_);
return v___x_313_;
}
case 1:
{
lean_object* v_node_314_; size_t v___x_315_; size_t v___x_316_; 
v_node_314_ = lean_ctor_get(v___x_311_, 0);
v___x_315_ = ((size_t)5ULL);
v___x_316_ = lean_usize_shift_right(v_x_304_, v___x_315_);
v_x_303_ = v_node_314_;
v_x_304_ = v___x_316_;
goto _start;
}
default: 
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
else
{
lean_object* v_ks_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_ks_319_ = lean_ctor_get(v_x_303_, 0);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_ks_319_, v___x_320_, v_x_305_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
size_t v_x_4372__boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v_x_4372__boxed_325_ = lean_unbox_usize(v_x_323_);
lean_dec(v_x_323_);
v_res_326_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_322_, v_x_4372__boxed_325_, v_x_324_);
lean_dec(v_x_324_);
lean_dec_ref(v_x_322_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint64_t v___x_330_; size_t v___x_331_; uint8_t v___x_332_; 
v___x_330_ = l_Lean_instHashableMVarId_hash(v_x_329_);
v___x_331_ = lean_uint64_to_usize(v___x_330_);
v___x_332_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_328_, v___x_331_, v_x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_333_, v_x_334_);
lean_dec(v_x_334_);
lean_dec_ref(v_x_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v_mctx_341_; lean_object* v_eAssignment_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_340_ = lean_st_ref_get(v___y_338_);
v_mctx_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_mctx_341_);
lean_dec(v___x_340_);
v_eAssignment_342_ = lean_ctor_get(v_mctx_341_, 8);
lean_inc_ref(v_eAssignment_342_);
lean_dec_ref(v_mctx_341_);
v___x_343_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_eAssignment_342_, v_mvarId_337_);
lean_dec_ref(v_eAssignment_342_);
v___x_344_ = lean_box(v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec(v_mvarId_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
return v_x_350_;
}
else
{
lean_object* v_head_352_; lean_object* v_tail_353_; lean_object* v___x_354_; 
v_head_352_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_head_352_);
v_tail_353_ = lean_ctor_get(v_x_351_, 1);
lean_inc(v_tail_353_);
lean_dec_ref_known(v_x_351_, 2);
v___x_354_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_350_, v_head_352_);
v_x_350_ = v___x_354_;
v_x_351_ = v_tail_353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(lean_object* v_f_356_, lean_object* v_a_357_, uint8_t v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
if (lean_obj_tag(v_a_359_) == 0)
{
if (lean_obj_tag(v_a_360_) == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_a_357_);
lean_dec_ref(v_f_356_);
v___x_371_ = lean_box(v_a_358_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_361_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v_head_374_; lean_object* v_tail_375_; 
v_head_374_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_head_374_);
v_tail_375_ = lean_ctor_get(v_a_360_, 1);
lean_inc(v_tail_375_);
lean_dec_ref_known(v_a_360_, 2);
v_a_359_ = v_head_374_;
v_a_360_ = v_tail_375_;
goto _start;
}
}
else
{
lean_object* v_head_377_; lean_object* v_tail_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_421_; 
v_head_377_ = lean_ctor_get(v_a_359_, 0);
v_tail_378_ = lean_ctor_get(v_a_359_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_359_);
if (v_isSharedCheck_421_ == 0)
{
v___x_380_ = v_a_359_;
v_isShared_381_ = v_isSharedCheck_421_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_tail_378_);
lean_inc(v_head_377_);
lean_dec(v_a_359_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_421_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_420_; 
v___x_382_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_head_377_, v___y_367_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_420_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_420_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_420_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint8_t v___x_387_; 
v___x_387_ = lean_unbox(v_a_383_);
lean_dec(v_a_383_);
if (v___x_387_ == 0)
{
lean_object* v_zero_388_; uint8_t v_isZero_389_; 
v_zero_388_ = lean_unsigned_to_nat(0u);
v_isZero_389_ = lean_nat_dec_eq(v_a_357_, v_zero_388_);
if (v_isZero_389_ == 1)
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
lean_del_object(v___x_380_);
lean_dec(v_a_357_);
lean_dec_ref(v_f_356_);
v___x_390_ = lean_array_push(v_a_361_, v_head_377_);
v___x_391_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_390_, v_tail_378_);
v___x_392_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(v___x_391_, v_a_360_);
v___x_393_ = lean_box(v_a_358_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_394_);
v___x_396_ = v___x_385_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
else
{
lean_object* v_one_398_; lean_object* v_n_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_del_object(v___x_385_);
v_one_398_ = lean_unsigned_to_nat(1u);
v_n_399_ = lean_nat_sub(v_a_357_, v_one_398_);
lean_dec(v_a_357_);
v___x_400_ = 1;
lean_inc_ref(v_f_356_);
lean_inc(v_head_377_);
v___x_401_ = lean_apply_1(v_f_356_, v_head_377_);
v___x_402_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v___x_401_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
if (lean_obj_tag(v_a_403_) == 0)
{
lean_object* v___x_404_; 
lean_del_object(v___x_380_);
v___x_404_ = lean_array_push(v_a_361_, v_head_377_);
v_a_357_ = v_n_399_;
v_a_359_ = v_tail_378_;
v_a_361_ = v___x_404_;
goto _start;
}
else
{
lean_object* v_val_406_; lean_object* v___x_408_; 
lean_dec(v_head_377_);
v_val_406_ = lean_ctor_get(v_a_403_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_a_403_, 1);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_a_360_);
lean_ctor_set(v___x_380_, 0, v_tail_378_);
v___x_408_ = v___x_380_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_tail_378_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_a_360_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v_a_357_ = v_n_399_;
v_a_358_ = v___x_400_;
v_a_359_ = v_val_406_;
v_a_360_ = v___x_408_;
goto _start;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_n_399_);
lean_del_object(v___x_380_);
lean_dec(v_tail_378_);
lean_dec(v_head_377_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_f_356_);
v_a_411_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_402_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_402_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_del_object(v___x_385_);
lean_del_object(v___x_380_);
lean_dec(v_head_377_);
v_a_359_ = v_tail_378_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_f_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v_a_4451__boxed_437_; lean_object* v_res_438_; 
v_a_4451__boxed_437_ = lean_unbox(v_a_424_);
v_res_438_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_422_, v_a_423_, v_a_4451__boxed_437_, v_a_425_, v_a_426_, v_a_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_a_453_; uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
v___x_459_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v___x_458_, v___y_448_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; uint8_t v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_inc(v___x_458_);
v___x_462_ = lean_array_push(v_b_442_, v___x_458_);
v_a_453_ = v___x_462_;
goto v___jp_452_;
}
else
{
v_a_453_ = v_b_442_;
goto v___jp_452_;
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_b_442_);
v_a_463_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_459_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_459_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_b_442_);
return v___x_471_;
}
v___jp_452_:
{
size_t v___x_454_; size_t v___x_455_; 
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_440_, v___x_454_);
v_i_440_ = v___x_455_;
v_b_442_ = v_a_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_stop_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
size_t v_i_boxed_485_; size_t v_stop_boxed_486_; lean_object* v_res_487_; 
v_i_boxed_485_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_stop_boxed_486_ = lean_unbox_usize(v_stop_474_);
lean_dec(v_stop_474_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_472_, v_i_boxed_485_, v_stop_boxed_486_, v_b_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v_as_472_);
return v_res_487_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0));
v___x_491_ = lean_array_to_list(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(lean_object* v_f_492_, lean_object* v_goals_493_, lean_object* v_maxIters_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = 0;
v___x_505_ = lean_box(0);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0));
v___x_508_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_492_, v_maxIters_494_, v___x_504_, v_goals_493_, v___x_505_, v___x_507_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_551_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_551_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_551_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_551_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_550_; 
v_fst_513_ = lean_ctor_get(v_a_509_, 0);
v_snd_514_ = lean_ctor_get(v_a_509_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_550_ == 0)
{
v___x_516_ = v_a_509_;
v_isShared_517_ = v_isSharedCheck_550_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_inc(v_fst_513_);
lean_dec(v_a_509_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_550_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_get_size(v_snd_514_);
v___x_519_ = lean_nat_dec_lt(v___x_506_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_snd_514_);
v___x_520_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_520_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_fst_513_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_522_);
v___x_524_ = v___x_511_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
lean_del_object(v___x_511_);
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_518_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_514_, v___x_527_, v___x_528_, v___x_507_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v_snd_514_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_array_to_list(v_a_530_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_534_);
v___x_536_ = v___x_516_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_513_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_536_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_516_);
lean_dec(v_fst_513_);
v_a_542_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_529_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_529_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_508_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_508_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed(lean_object* v_f_560_, lean_object* v_goals_561_, lean_object* v_maxIters_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_560_, v_goals_561_, v_maxIters_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(lean_object* v_x_573_){
_start:
{
lean_object* v_snd_574_; 
v_snd_574_ = lean_ctor_get(v_x_573_, 1);
lean_inc(v_snd_574_);
return v_snd_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(v_x_575_);
lean_dec_ref(v_x_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(lean_object* v_a_577_, lean_object* v_f_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
v___x_588_ = lean_apply_9(v_a_577_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, lean_box(0));
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_apply_1(v_f_578_, v_a_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_f_578_);
v_a_598_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_588_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_588_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg___boxed(lean_object* v_a_606_, lean_object* v_f_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_606_, v_f_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(lean_object* v_f_619_, lean_object* v_goals_620_, lean_object* v_maxIters_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___f_631_ = ((lean_object*)(l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0));
v___x_632_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed), 12, 3);
lean_closure_set(v___x_632_, 0, v_f_619_);
lean_closure_set(v___x_632_, 1, v_goals_620_);
lean_closure_set(v___x_632_, 2, v_maxIters_621_);
v___x_633_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v___x_632_, v___f_631_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(lean_object* v_f_634_, lean_object* v_goals_635_, lean_object* v_maxIters_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v_f_634_, v_goals_635_, v_maxIters_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27(lean_object* v_stx_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1));
lean_inc(v_stx_653_);
v___x_664_ = l_Lean_Syntax_isOfKind(v_stx_653_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v_stx_653_);
v___x_665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = l_Lean_Syntax_getArg(v_stx_653_, v___x_666_);
lean_dec(v_stx_653_);
v___x_668_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_667_);
v___x_669_ = l_Lean_Syntax_isOfKind(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_667_);
v___x_670_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_670_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_655_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw___boxed), 11, 1);
lean_closure_set(v___x_673_, 0, v___x_667_);
v___x_674_ = lean_unsigned_to_nat(100000u);
v___x_675_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v___x_673_, v_a_672_, v___x_674_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_676_, v_a_655_);
return v___x_677_;
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_675_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec(v___x_667_);
v_a_686_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_671_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_671_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27___boxed(lean_object* v_stx_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Elab_Tactic_evalRepeat_x27(v_stx_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_a_707_, lean_object* v_f_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_707_, v_f_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(lean_object* v_00_u03b1_719_, lean_object* v_00_u03b2_720_, lean_object* v_a_721_, lean_object* v_f_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(v_00_u03b1_719_, v_00_u03b2_720_, v_a_721_, v_f_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_733_, lean_object* v_x_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(lean_object* v_mvarId_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_757_, v___y_763_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v_mvarId_768_);
return v_res_778_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_780_, v_x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_783_, v_x_784_, v_x_785_);
lean_dec(v_x_785_);
lean_dec_ref(v_x_784_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, size_t v_x_790_, lean_object* v_x_791_){
_start:
{
uint8_t v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
size_t v_x_5097__boxed_797_; uint8_t v_res_798_; lean_object* v_r_799_; 
v_x_5097__boxed_797_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_res_798_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_793_, v_x_794_, v_x_5097__boxed_797_, v_x_796_);
lean_dec(v_x_796_);
lean_dec_ref(v_x_794_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_800_, lean_object* v_keys_801_, lean_object* v_vals_802_, lean_object* v_heq_803_, lean_object* v_i_804_, lean_object* v_k_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_801_, v_i_804_, v_k_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_807_, lean_object* v_keys_808_, lean_object* v_vals_809_, lean_object* v_heq_810_, lean_object* v_i_811_, lean_object* v_k_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(v_00_u03b2_807_, v_keys_808_, v_vals_809_, v_heq_810_, v_i_811_, v_k_812_);
lean_dec(v_k_812_);
lean_dec_ref(v_vals_809_);
lean_dec_ref(v_keys_808_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1(){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_822_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_823_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1));
v___x_824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1));
v___x_825_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat_x27___boxed), 10, 0);
v___x_826_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_822_, v___x_823_, v___x_824_, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___boxed(lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3(){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1));
v___x_856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6));
v___x_857_ = l_Lean_addBuiltinDeclarationRanges(v___x_855_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(lean_object* v_msgData_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_env_867_; uint8_t v___x_868_; lean_object* v_env_869_; lean_object* v___x_870_; lean_object* v_toCold_871_; lean_object* v_mctx_872_; lean_object* v_lctx_873_; lean_object* v_options_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_866_ = lean_st_ref_get(v___y_864_);
v_env_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_env_867_);
lean_dec(v___x_866_);
v___x_868_ = 0;
v_env_869_ = l_Lean_Environment_setRecordingDeps(v_env_867_, v___x_868_);
v___x_870_ = lean_st_ref_get(v___y_862_);
v_toCold_871_ = lean_ctor_get(v___y_863_, 0);
v_mctx_872_ = lean_ctor_get(v___x_870_, 0);
lean_inc_ref(v_mctx_872_);
lean_dec(v___x_870_);
v_lctx_873_ = lean_ctor_get(v___y_861_, 2);
v_options_874_ = lean_ctor_get(v_toCold_871_, 2);
lean_inc_ref(v_options_874_);
lean_inc_ref(v_lctx_873_);
v___x_875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_875_, 0, v_env_869_);
lean_ctor_set(v___x_875_, 1, v_mctx_872_);
lean_ctor_set(v___x_875_, 2, v_lctx_873_);
lean_ctor_set(v___x_875_, 3, v_options_874_);
v___x_876_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_msgData_860_);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(lean_object* v_msg_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
v_ref_891_ = lean_ctor_get(v___y_888_, 2);
v___x_892_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msg_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_901_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_inc(v_ref_891_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_ref_891_);
lean_ctor_set(v___x_897_, 1, v_a_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 1);
lean_ctor_set(v___x_895_, 0, v___x_897_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg___boxed(lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(lean_object* v_f_912_, lean_object* v_goals_913_, lean_object* v_maxIters_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_912_, v_goals_913_, v_maxIters_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_fst_929_; uint8_t v___x_930_; 
v_fst_929_ = lean_ctor_get(v_a_925_, 0);
v___x_930_ = lean_unbox(v_fst_929_);
if (v___x_930_ == 1)
{
lean_object* v_snd_931_; lean_object* v___x_933_; 
v_snd_931_ = lean_ctor_get(v_a_925_, 1);
lean_inc(v_snd_931_);
lean_dec(v_a_925_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_snd_931_);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_snd_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_927_);
lean_dec(v_a_925_);
v___x_935_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1);
v___x_936_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v___x_935_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_936_;
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_924_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_924_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___boxed(lean_object* v_f_946_, lean_object* v_goals_947_, lean_object* v_maxIters_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v_f_946_, v_goals_947_, v_maxIters_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27(lean_object* v_stx_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1));
lean_inc(v_stx_965_);
v___x_976_ = l_Lean_Syntax_isOfKind(v_stx_965_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_stx_965_);
v___x_977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = l_Lean_Syntax_getArg(v_stx_965_, v___x_978_);
lean_dec(v_stx_965_);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_979_);
v___x_981_ = l_Lean_Syntax_isOfKind(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec(v___x_979_);
v___x_982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_967_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw___boxed), 11, 1);
lean_closure_set(v___x_985_, 0, v___x_979_);
v___x_986_ = lean_unsigned_to_nat(100000u);
v___x_987_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v___x_985_, v_a_984_, v___x_986_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_988_, v_a_967_);
return v___x_989_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v_a_990_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_987_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_987_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v___x_979_);
v_a_998_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_983_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_983_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27___boxed(lean_object* v_stx_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Elab_Tactic_evalRepeat1_x27(v_stx_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(lean_object* v_00_u03b1_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_1018_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(v_00_u03b1_1029_, v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1(){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1));
v___x_1050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1));
v___x_1051_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat1_x27___boxed), 10, 0);
v___x_1052_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1048_, v___x_1049_, v___x_1050_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___boxed(lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3(){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1));
v___x_1082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6));
v___x_1083_ = l_Lean_addBuiltinDeclarationRanges(v___x_1081_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
return v_res_1085_;
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
