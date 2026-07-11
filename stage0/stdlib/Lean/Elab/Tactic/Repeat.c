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
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_33_, v___y_35_, v___y_37_, v___y_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_43_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_a_42_);
lean_dec_ref_known(v___x_41_, 1);
lean_inc(v___x_31_);
v___x_43_ = l_Lean_Elab_Tactic_evalTactic(v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_dec_ref_known(v___x_43_, 1);
lean_dec(v_a_42_);
goto _start;
}
else
{
lean_object* v_a_45_; lean_object* v___x_46_; uint8_t v___y_48_; uint8_t v___x_58_; 
lean_dec(v___x_31_);
v_a_45_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_45_);
v___x_46_ = lean_box(0);
v___x_58_ = l_Lean_Exception_isInterrupt(v_a_45_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_Exception_isRuntime(v_a_45_);
v___y_48_ = v___x_59_;
goto v___jp_47_;
}
else
{
lean_dec(v_a_45_);
v___y_48_ = v___x_58_;
goto v___jp_47_;
}
v___jp_47_:
{
if (v___y_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec_ref_known(v___x_43_, 1);
v___x_49_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_42_, v___y_48_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
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
lean_ctor_set(v___x_51_, 0, v___x_46_);
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_46_);
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
lean_dec(v_a_42_);
return v___x_43_;
}
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec(v___x_31_);
v_a_60_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_41_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_41_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg___boxed(lean_object* v___x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0(lean_object* v___x_79_, lean_object* v___x_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_79_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v___x_90_, 0);
lean_dec(v_unused_98_);
v___x_92_ = v___x_90_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_dec(v___x_90_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_80_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_80_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed(lean_object* v___x_99_, lean_object* v___x_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_Tactic_evalRepeat___lam__0(v___x_99_, v___x_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat(lean_object* v_stx_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__4));
lean_inc(v_stx_126_);
v___x_137_ = l_Lean_Syntax_isOfKind(v_stx_126_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_dec(v_stx_126_);
v___x_138_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = l_Lean_Syntax_getArg(v_stx_126_, v___x_139_);
lean_dec(v_stx_126_);
v___x_141_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_140_);
v___x_142_ = l_Lean_Syntax_isOfKind(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_dec(v___x_140_);
v___x_143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed), 11, 2);
lean_closure_set(v___f_145_, 0, v___x_140_);
lean_closure_set(v___f_145_, 1, v___x_144_);
v___x_146_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_145_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat___boxed(lean_object* v_stx_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Elab_Tactic_evalRepeat(v_stx_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(lean_object* v___x_158_, lean_object* v_inst_159_, lean_object* v_a_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_158_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(lean_object* v___x_171_, lean_object* v_inst_172_, lean_object* v_a_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(v___x_171_, v_inst_172_, v_a_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1(){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_193_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__4));
v___x_194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2));
v___x_195_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat___boxed), 10, 0);
v___x_196_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_192_, v___x_193_, v___x_194_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___boxed(lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_201_, v___y_203_, v___y_205_, v___y_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_201_, v___y_203_, v___y_205_, v___y_207_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
lean_inc(v___y_205_);
lean_inc_ref(v___y_204_);
lean_inc(v___y_203_);
lean_inc_ref(v___y_202_);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
v___x_213_ = lean_apply_9(v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_a_212_);
lean_dec(v_a_210_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_a_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_261_; 
v_a_223_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_261_ == 0)
{
v___x_225_ = v___x_213_;
v_isShared_226_ = v_isSharedCheck_261_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_213_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_261_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint8_t v___y_228_; uint8_t v___x_259_; 
v___x_259_ = l_Lean_Exception_isInterrupt(v_a_223_);
if (v___x_259_ == 0)
{
uint8_t v___x_260_; 
lean_inc(v_a_223_);
v___x_260_ = l_Lean_Exception_isRuntime(v_a_223_);
v___y_228_ = v___x_260_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___x_259_;
goto v___jp_227_;
}
v___jp_227_:
{
if (v___y_228_ == 0)
{
lean_object* v___x_229_; 
lean_del_object(v___x_225_);
lean_dec(v_a_223_);
v___x_229_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_212_, v___y_228_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
lean_dec_ref_known(v___x_229_, 1);
v___x_230_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_210_, v___y_228_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_238_; 
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v___x_230_, 0);
lean_dec(v_unused_239_);
v___x_232_ = v___x_230_;
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
else
{
lean_dec(v___x_230_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_box(0);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_a_240_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_230_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_230_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_210_);
v_a_248_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_229_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_229_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v___x_257_; 
lean_dec(v_a_212_);
lean_dec(v_a_210_);
if (v_isShared_226_ == 0)
{
v___x_257_ = v___x_225_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_223_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_a_210_);
lean_dec_ref(v_x_199_);
v_a_262_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_211_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_211_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_x_199_);
v_a_270_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_209_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_209_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(lean_object* v_keys_289_, lean_object* v_i_290_, lean_object* v_k_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_get_size(v_keys_289_);
v___x_293_ = lean_nat_dec_lt(v_i_290_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec(v_i_290_);
return v___x_293_;
}
else
{
lean_object* v_k_x27_294_; uint8_t v___x_295_; 
v_k_x27_294_ = lean_array_fget_borrowed(v_keys_289_, v_i_290_);
v___x_295_ = l_Lean_instBEqMVarId_beq(v_k_291_, v_k_x27_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_i_290_, v___x_296_);
lean_dec(v_i_290_);
v_i_290_ = v___x_297_;
goto _start;
}
else
{
lean_dec(v_i_290_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_keys_299_, lean_object* v_i_300_, lean_object* v_k_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_299_, v_i_300_, v_k_301_);
lean_dec(v_k_301_);
lean_dec_ref(v_keys_299_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(lean_object* v_x_304_, size_t v_x_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v_es_307_; lean_object* v___x_308_; size_t v___x_309_; size_t v___x_310_; lean_object* v_j_311_; lean_object* v___x_312_; 
v_es_307_ = lean_ctor_get(v_x_304_, 0);
v___x_308_ = lean_box(2);
v___x_309_ = ((size_t)31ULL);
v___x_310_ = lean_usize_land(v_x_305_, v___x_309_);
v_j_311_ = lean_usize_to_nat(v___x_310_);
v___x_312_ = lean_array_get_borrowed(v___x_308_, v_es_307_, v_j_311_);
lean_dec(v_j_311_);
switch(lean_obj_tag(v___x_312_))
{
case 0:
{
lean_object* v_key_313_; uint8_t v___x_314_; 
v_key_313_ = lean_ctor_get(v___x_312_, 0);
v___x_314_ = l_Lean_instBEqMVarId_beq(v_x_306_, v_key_313_);
return v___x_314_;
}
case 1:
{
lean_object* v_node_315_; size_t v___x_316_; size_t v___x_317_; 
v_node_315_ = lean_ctor_get(v___x_312_, 0);
v___x_316_ = ((size_t)5ULL);
v___x_317_ = lean_usize_shift_right(v_x_305_, v___x_316_);
v_x_304_ = v_node_315_;
v_x_305_ = v___x_317_;
goto _start;
}
default: 
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
}
}
else
{
lean_object* v_ks_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_ks_320_ = lean_ctor_get(v_x_304_, 0);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_ks_320_, v___x_321_, v_x_306_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
size_t v_x_4722__boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_x_4722__boxed_326_ = lean_unbox_usize(v_x_324_);
lean_dec(v_x_324_);
v_res_327_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_323_, v_x_4722__boxed_326_, v_x_325_);
lean_dec(v_x_325_);
lean_dec_ref(v_x_323_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint64_t v___x_331_; size_t v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_instHashableMVarId_hash(v_x_330_);
v___x_332_ = lean_uint64_to_usize(v___x_331_);
v___x_333_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_329_, v___x_332_, v_x_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_334_, v_x_335_);
lean_dec(v_x_335_);
lean_dec_ref(v_x_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_mctx_342_; lean_object* v_eAssignment_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = lean_st_ref_get(v___y_339_);
v_mctx_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_mctx_342_);
lean_dec(v___x_341_);
v_eAssignment_343_ = lean_ctor_get(v_mctx_342_, 8);
lean_inc_ref(v_eAssignment_343_);
lean_dec_ref(v_mctx_342_);
v___x_344_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_eAssignment_343_, v_mvarId_338_);
lean_dec_ref(v_eAssignment_343_);
v___x_345_ = lean_box(v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec(v_mvarId_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
return v_x_351_;
}
else
{
lean_object* v_head_353_; lean_object* v_tail_354_; lean_object* v___x_355_; 
v_head_353_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_head_353_);
v_tail_354_ = lean_ctor_get(v_x_352_, 1);
lean_inc(v_tail_354_);
lean_dec_ref_known(v_x_352_, 2);
v___x_355_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_351_, v_head_353_);
v_x_351_ = v___x_355_;
v_x_352_ = v_tail_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(lean_object* v_f_357_, lean_object* v_a_358_, uint8_t v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
if (lean_obj_tag(v_a_360_) == 0)
{
if (lean_obj_tag(v_a_361_) == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_a_358_);
lean_dec_ref(v_f_357_);
v___x_372_ = lean_box(v_a_359_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_a_362_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
else
{
lean_object* v_head_375_; lean_object* v_tail_376_; 
v_head_375_ = lean_ctor_get(v_a_361_, 0);
lean_inc(v_head_375_);
v_tail_376_ = lean_ctor_get(v_a_361_, 1);
lean_inc(v_tail_376_);
lean_dec_ref_known(v_a_361_, 2);
v_a_360_ = v_head_375_;
v_a_361_ = v_tail_376_;
goto _start;
}
}
else
{
lean_object* v_head_378_; lean_object* v_tail_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_422_; 
v_head_378_ = lean_ctor_get(v_a_360_, 0);
v_tail_379_ = lean_ctor_get(v_a_360_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_422_ == 0)
{
v___x_381_ = v_a_360_;
v_isShared_382_ = v_isSharedCheck_422_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_tail_379_);
lean_inc(v_head_378_);
lean_dec(v_a_360_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_422_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_421_; 
v___x_383_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_head_378_, v___y_368_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_421_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_421_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_421_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint8_t v___x_388_; 
v___x_388_ = lean_unbox(v_a_384_);
lean_dec(v_a_384_);
if (v___x_388_ == 0)
{
lean_object* v_zero_389_; uint8_t v_isZero_390_; 
v_zero_389_ = lean_unsigned_to_nat(0u);
v_isZero_390_ = lean_nat_dec_eq(v_a_358_, v_zero_389_);
if (v_isZero_390_ == 1)
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
lean_del_object(v___x_381_);
lean_dec(v_a_358_);
lean_dec_ref(v_f_357_);
v___x_391_ = lean_array_push(v_a_362_, v_head_378_);
v___x_392_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_391_, v_tail_379_);
v___x_393_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(v___x_392_, v_a_361_);
v___x_394_ = lean_box(v_a_359_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_395_);
v___x_397_ = v___x_386_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_del_object(v___x_386_);
lean_inc_ref(v_f_357_);
lean_inc(v_head_378_);
v___x_399_ = lean_apply_1(v_f_357_, v_head_378_);
v___x_400_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v___x_399_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_one_402_; lean_object* v_n_403_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v_one_402_ = lean_unsigned_to_nat(1u);
v_n_403_ = lean_nat_sub(v_a_358_, v_one_402_);
lean_dec(v_a_358_);
if (lean_obj_tag(v_a_401_) == 0)
{
lean_object* v___x_404_; 
lean_del_object(v___x_381_);
v___x_404_ = lean_array_push(v_a_362_, v_head_378_);
v_a_358_ = v_n_403_;
v_a_360_ = v_tail_379_;
v_a_362_ = v___x_404_;
goto _start;
}
else
{
lean_object* v_val_406_; uint8_t v___x_407_; lean_object* v___x_409_; 
lean_dec(v_head_378_);
v_val_406_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_a_401_, 1);
v___x_407_ = 1;
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v_a_361_);
lean_ctor_set(v___x_381_, 0, v_tail_379_);
v___x_409_ = v___x_381_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_tail_379_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_a_361_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
v_a_358_ = v_n_403_;
v_a_359_ = v___x_407_;
v_a_360_ = v_val_406_;
v_a_361_ = v___x_409_;
goto _start;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_del_object(v___x_381_);
lean_dec(v_tail_379_);
lean_dec(v_head_378_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec(v_a_358_);
lean_dec_ref(v_f_357_);
v_a_412_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_400_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_400_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
else
{
lean_del_object(v___x_386_);
lean_del_object(v___x_381_);
lean_dec(v_head_378_);
v_a_360_ = v_tail_379_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_f_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v_a_4801__boxed_438_; lean_object* v_res_439_; 
v_a_4801__boxed_438_ = lean_unbox(v_a_425_);
v_res_439_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_423_, v_a_424_, v_a_4801__boxed_438_, v_a_426_, v_a_427_, v_a_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(lean_object* v_as_440_, size_t v_i_441_, size_t v_stop_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_a_454_; uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_eq(v_i_441_, v_stop_442_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; uint8_t v_a_461_; lean_object* v___x_463_; 
v___x_459_ = lean_array_uget_borrowed(v_as_440_, v_i_441_);
v___x_463_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v___x_459_, v___y_449_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; uint8_t v___x_465_; uint8_t v___x_466_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = lean_unbox(v_a_464_);
lean_dec(v_a_464_);
v___x_466_ = lean_bool_not(v___x_465_);
v_a_461_ = v___x_466_;
goto v___jp_460_;
}
else
{
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_467_; uint8_t v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_463_, 1);
v___x_468_ = lean_unbox(v_a_467_);
lean_dec(v_a_467_);
v_a_461_ = v___x_468_;
goto v___jp_460_;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_b_443_);
v_a_469_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_463_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_463_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
v___jp_460_:
{
if (v_a_461_ == 0)
{
v_a_454_ = v_b_443_;
goto v___jp_453_;
}
else
{
lean_object* v___x_462_; 
lean_inc(v___x_459_);
v___x_462_ = lean_array_push(v_b_443_, v___x_459_);
v_a_454_ = v___x_462_;
goto v___jp_453_;
}
}
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_b_443_);
return v___x_477_;
}
v___jp_453_:
{
size_t v___x_455_; size_t v___x_456_; 
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_441_, v___x_455_);
v_i_441_ = v___x_456_;
v_b_443_ = v_a_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(lean_object* v_as_478_, lean_object* v_i_479_, lean_object* v_stop_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
size_t v_i_boxed_491_; size_t v_stop_boxed_492_; lean_object* v_res_493_; 
v_i_boxed_491_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_stop_boxed_492_ = lean_unbox_usize(v_stop_480_);
lean_dec(v_stop_480_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_478_, v_i_boxed_491_, v_stop_boxed_492_, v_b_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_as_478_);
return v_res_493_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0));
v___x_497_ = lean_array_to_list(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(lean_object* v_f_498_, lean_object* v_goals_499_, lean_object* v_maxIters_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_510_ = 0;
v___x_511_ = lean_box(0);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0));
v___x_514_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_498_, v_maxIters_500_, v___x_510_, v_goals_499_, v___x_511_, v___x_513_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_564_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_564_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_564_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_564_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_563_; 
v_fst_519_ = lean_ctor_get(v_a_515_, 0);
v_snd_520_ = lean_ctor_get(v_a_515_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_563_ == 0)
{
v___x_522_ = v_a_515_;
v_isShared_523_ = v_isSharedCheck_563_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_inc(v_fst_519_);
lean_dec(v_a_515_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_563_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_____do__lift_525_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_array_get_size(v_snd_520_);
v___x_534_ = lean_nat_dec_lt(v___x_512_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_del_object(v___x_522_);
lean_dec(v_snd_520_);
lean_del_object(v___x_517_);
v___x_535_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_fst_519_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
else
{
uint8_t v___x_538_; 
v___x_538_ = lean_nat_dec_le(v___x_533_, v___x_533_);
if (v___x_538_ == 0)
{
if (v___x_534_ == 0)
{
lean_dec(v_snd_520_);
v_____do__lift_525_ = v___x_513_;
goto v___jp_524_;
}
else
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((size_t)0ULL);
v___x_540_ = lean_usize_of_nat(v___x_533_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_520_, v___x_539_, v___x_540_, v___x_513_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v_snd_520_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v_____do__lift_525_ = v_a_542_;
goto v___jp_524_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_del_object(v___x_522_);
lean_dec(v_fst_519_);
lean_del_object(v___x_517_);
v_a_543_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_541_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_533_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_520_, v___x_551_, v___x_552_, v___x_513_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v_snd_520_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v_____do__lift_525_ = v_a_554_;
goto v___jp_524_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_522_);
lean_dec(v_fst_519_);
lean_del_object(v___x_517_);
v_a_555_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_553_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_array_to_list(v_____do__lift_525_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_526_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_528_);
v___x_530_ = v___x_517_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_514_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_514_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed(lean_object* v_f_573_, lean_object* v_goals_574_, lean_object* v_maxIters_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_573_, v_goals_574_, v_maxIters_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(lean_object* v_x_586_){
_start:
{
lean_object* v_snd_587_; 
v_snd_587_ = lean_ctor_get(v_x_586_, 1);
lean_inc(v_snd_587_);
return v_snd_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(lean_object* v_x_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(v_x_588_);
lean_dec_ref(v_x_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(lean_object* v_a_590_, lean_object* v_f_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
lean_inc_ref(v___y_596_);
lean_inc(v___y_595_);
lean_inc_ref(v___y_594_);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
v___x_601_ = lean_apply_9(v_a_590_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, lean_box(0));
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_apply_1(v_f_591_, v_a_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_f_591_);
v_a_611_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_601_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg___boxed(lean_object* v_a_619_, lean_object* v_f_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_619_, v_f_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(lean_object* v_f_632_, lean_object* v_goals_633_, lean_object* v_maxIters_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___f_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___f_644_ = ((lean_object*)(l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0));
v___x_645_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed), 12, 3);
lean_closure_set(v___x_645_, 0, v_f_632_);
lean_closure_set(v___x_645_, 1, v_goals_633_);
lean_closure_set(v___x_645_, 2, v_maxIters_634_);
v___x_646_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v___x_645_, v___f_644_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(lean_object* v_f_647_, lean_object* v_goals_648_, lean_object* v_maxIters_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v_f_647_, v_goals_648_, v_maxIters_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27(lean_object* v_stx_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1));
lean_inc(v_stx_666_);
v___x_677_ = l_Lean_Syntax_isOfKind(v_stx_666_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec(v_stx_666_);
v___x_678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = l_Lean_Syntax_getArg(v_stx_666_, v___x_679_);
lean_dec(v_stx_666_);
v___x_681_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_isOfKind(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec(v___x_680_);
v___x_683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_668_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw___boxed), 11, 1);
lean_closure_set(v___x_686_, 0, v___x_680_);
v___x_687_ = lean_unsigned_to_nat(100000u);
v___x_688_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v___x_686_, v_a_685_, v___x_687_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_689_, v_a_668_);
return v___x_690_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_688_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_688_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v___x_680_);
v_a_699_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_684_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_684_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27___boxed(lean_object* v_stx_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Elab_Tactic_evalRepeat_x27(v_stx_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_a_720_, lean_object* v_f_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_720_, v_f_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_a_734_, lean_object* v_f_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(v_00_u03b1_732_, v_00_u03b2_733_, v_a_734_, v_f_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_758_, v_x_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(lean_object* v_mvarId_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_770_, v___y_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v_mvarId_781_);
return v_res_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_796_, v_x_797_, v_x_798_);
lean_dec(v_x_798_);
lean_dec_ref(v_x_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, size_t v_x_803_, lean_object* v_x_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_802_, v_x_803_, v_x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
size_t v_x_5471__boxed_810_; uint8_t v_res_811_; lean_object* v_r_812_; 
v_x_5471__boxed_810_ = lean_unbox_usize(v_x_808_);
lean_dec(v_x_808_);
v_res_811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_806_, v_x_807_, v_x_5471__boxed_810_, v_x_809_);
lean_dec(v_x_809_);
lean_dec_ref(v_x_807_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_813_, lean_object* v_keys_814_, lean_object* v_vals_815_, lean_object* v_heq_816_, lean_object* v_i_817_, lean_object* v_k_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_814_, v_i_817_, v_k_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_820_, lean_object* v_keys_821_, lean_object* v_vals_822_, lean_object* v_heq_823_, lean_object* v_i_824_, lean_object* v_k_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(v_00_u03b2_820_, v_keys_821_, v_vals_822_, v_heq_823_, v_i_824_, v_k_825_);
lean_dec(v_k_825_);
lean_dec_ref(v_vals_822_);
lean_dec_ref(v_keys_821_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1(){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_835_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_836_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1));
v___x_837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1));
v___x_838_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat_x27___boxed), 10, 0);
v___x_839_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_835_, v___x_836_, v___x_837_, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___boxed(lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3(){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1));
v___x_869_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6));
v___x_870_ = l_Lean_addBuiltinDeclarationRanges(v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(lean_object* v_msgData_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_env_880_; lean_object* v___x_881_; lean_object* v_mctx_882_; lean_object* v_lctx_883_; lean_object* v_options_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_879_ = lean_st_ref_get(v___y_877_);
v_env_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc_ref(v_env_880_);
lean_dec(v___x_879_);
v___x_881_ = lean_st_ref_get(v___y_875_);
v_mctx_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc_ref(v_mctx_882_);
lean_dec(v___x_881_);
v_lctx_883_ = lean_ctor_get(v___y_874_, 2);
v_options_884_ = lean_ctor_get(v___y_876_, 2);
lean_inc_ref(v_options_884_);
lean_inc_ref(v_lctx_883_);
v___x_885_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_885_, 0, v_env_880_);
lean_ctor_set(v___x_885_, 1, v_mctx_882_);
lean_ctor_set(v___x_885_, 2, v_lctx_883_);
lean_ctor_set(v___x_885_, 3, v_options_884_);
v___x_886_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v_msgData_873_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_ref_901_; lean_object* v___x_902_; lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_911_; 
v_ref_901_ = lean_ctor_get(v___y_898_, 5);
v___x_902_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_911_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
lean_inc(v_ref_901_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_ref_901_);
lean_ctor_set(v___x_907_, 1, v_a_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 1);
lean_ctor_set(v___x_905_, 0, v___x_907_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg___boxed(lean_object* v_msg_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(lean_object* v_f_922_, lean_object* v_goals_923_, lean_object* v_maxIters_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_922_, v_goals_923_, v_maxIters_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_947_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_947_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_947_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_947_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_fst_939_; uint8_t v___x_940_; 
v_fst_939_ = lean_ctor_get(v_a_935_, 0);
v___x_940_ = lean_unbox(v_fst_939_);
if (v___x_940_ == 1)
{
lean_object* v_snd_941_; lean_object* v___x_943_; 
v_snd_941_ = lean_ctor_get(v_a_935_, 1);
lean_inc(v_snd_941_);
lean_dec(v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_snd_941_);
v___x_943_ = v___x_937_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_snd_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_del_object(v___x_937_);
lean_dec(v_a_935_);
v___x_945_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1);
v___x_946_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v___x_945_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_946_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_934_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_934_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___boxed(lean_object* v_f_956_, lean_object* v_goals_957_, lean_object* v_maxIters_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v_f_956_, v_goals_957_, v_maxIters_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27(lean_object* v_stx_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1));
lean_inc(v_stx_975_);
v___x_986_ = l_Lean_Syntax_isOfKind(v_stx_975_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v_stx_975_);
v___x_987_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = l_Lean_Syntax_getArg(v_stx_975_, v___x_988_);
lean_dec(v_stx_975_);
v___x_990_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat___closed__6));
lean_inc(v___x_989_);
v___x_991_ = l_Lean_Syntax_isOfKind(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec(v___x_989_);
v___x_992_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
return v___x_992_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_977_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw___boxed), 11, 1);
lean_closure_set(v___x_995_, 0, v___x_989_);
v___x_996_ = lean_unsigned_to_nat(100000u);
v___x_997_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v___x_995_, v_a_994_, v___x_996_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_998_, v_a_977_);
return v___x_999_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_997_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_997_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v___x_989_);
v_a_1008_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_993_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_993_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27___boxed(lean_object* v_stx_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_Tactic_evalRepeat1_x27(v_stx_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(lean_object* v_00_u03b1_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_1028_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(v_00_u03b1_1039_, v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1(){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1));
v___x_1060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1));
v___x_1061_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat1_x27___boxed), 10, 0);
v___x_1062_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1058_, v___x_1059_, v___x_1060_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___boxed(lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3(){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6));
v___x_1093_ = l_Lean_addBuiltinDeclarationRanges(v___x_1091_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
return v_res_1095_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
