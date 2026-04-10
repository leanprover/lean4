// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Attr
// Imports: public import Lean.Meta.Tactic.Simp.Simproc
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstantKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Simp_ignoreEquations(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
extern lean_object* l_Lean_Meta_simpExtensionMapRef;
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_addDeclToUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_addDeclToUnfold___closed__0 = (const lean_object*)&l_Lean_Meta_addDeclToUnfold___closed__0_value;
static const lean_string_object l_Lean_Meta_addDeclToUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 23, .m_data = "Invalid `←` modifier: `"};
static const lean_object* l_Lean_Meta_addDeclToUnfold___closed__1 = (const lean_object*)&l_Lean_Meta_addDeclToUnfold___closed__1_value;
static lean_once_cell_t l_Lean_Meta_addDeclToUnfold___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDeclToUnfold___closed__2;
static const lean_string_object l_Lean_Meta_addDeclToUnfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "` is a declaration name to be unfolded"};
static const lean_object* l_Lean_Meta_addDeclToUnfold___closed__3 = (const lean_object*)&l_Lean_Meta_addDeclToUnfold___closed__3_value;
static lean_once_cell_t l_Lean_Meta_addDeclToUnfold___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDeclToUnfold___closed__4;
static const lean_string_object l_Lean_Meta_addDeclToUnfold___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 119, .m_capacity = 119, .m_length = 118, .m_data = "The simplifier will automatically unfold definitions marked with the `[simp]` attribute, but it will not \"refold\" them"};
static const lean_object* l_Lean_Meta_addDeclToUnfold___closed__5 = (const lean_object*)&l_Lean_Meta_addDeclToUnfold___closed__5_value;
static lean_once_cell_t l_Lean_Meta_addDeclToUnfold___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDeclToUnfold___closed__6;
static lean_once_cell_t l_Lean_Meta_addDeclToUnfold___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDeclToUnfold___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__1 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__2 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__3 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__4 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value;
static const lean_array_object l_Lean_Meta_mkSimpAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__5 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__5_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__6 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__7 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__8 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__9 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__9_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__10 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__11 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__12;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__13;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__14 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__14_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__15 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__16 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value;
static const lean_string_object l_Lean_Meta_mkSimpAttr___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__17 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__18;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__19;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__20;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__21;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__22;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__23;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__24;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__25;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__26;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__27;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___auto__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Cannot add `simp` attribute to `"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`: It is not a proposition nor a definition (to unfold)"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = "The `[simp]` attribute can be added to lemmas that should be automatically used by the simplifier and to definitions that the simplifier should automatically unfold"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__7;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__9;
static const lean_array_object l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__11;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__12;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__13;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__14;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "` does not have the `[simp]` attribute"};
static const lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "simplification theorem"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpExtension"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 178, 50, 159, 106, 143, 71, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtension;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "seval"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 151, 253, 192, 151, 99, 156, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "symbolic evaluator theorem"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "sevalSimpExtension"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 7, 7, 85, 34, 153, 50, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sevalSimpExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; uint8_t v___x_9_; uint8_t v___x_10_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = lean_unbox(v_val_6_);
v___x_9_ = lean_unbox(v_val_7_);
v___x_10_ = l_Lean_instBEqConstantKind_beq(v___x_8_, v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0___boxed(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(v_x_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_x_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_15_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
v___x_21_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
lean_ctor_set(v___x_21_, 2, v___x_20_);
lean_ctor_set(v___x_21_, 3, v___x_20_);
lean_ctor_set(v___x_21_, 4, v___x_20_);
lean_ctor_set(v___x_21_, 5, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(lean_object* v_ext_22_, lean_object* v_b_23_, uint8_t v_kind_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_currNamespace_29_; lean_object* v___x_30_; lean_object* v_env_31_; lean_object* v_nextMacroScope_32_; lean_object* v_ngen_33_; lean_object* v_auxDeclNGen_34_; lean_object* v_traceState_35_; lean_object* v_messages_36_; lean_object* v_infoState_37_; lean_object* v_snapshotTasks_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_65_; 
v_currNamespace_29_ = lean_ctor_get(v___y_26_, 6);
v___x_30_ = lean_st_ref_take(v___y_27_);
v_env_31_ = lean_ctor_get(v___x_30_, 0);
v_nextMacroScope_32_ = lean_ctor_get(v___x_30_, 1);
v_ngen_33_ = lean_ctor_get(v___x_30_, 2);
v_auxDeclNGen_34_ = lean_ctor_get(v___x_30_, 3);
v_traceState_35_ = lean_ctor_get(v___x_30_, 4);
v_messages_36_ = lean_ctor_get(v___x_30_, 6);
v_infoState_37_ = lean_ctor_get(v___x_30_, 7);
v_snapshotTasks_38_ = lean_ctor_get(v___x_30_, 8);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_30_, 5);
lean_dec(v_unused_66_);
v___x_40_ = v___x_30_;
v_isShared_41_ = v_isSharedCheck_65_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_snapshotTasks_38_);
lean_inc(v_infoState_37_);
lean_inc(v_messages_36_);
lean_inc(v_traceState_35_);
lean_inc(v_auxDeclNGen_34_);
lean_inc(v_ngen_33_);
lean_inc(v_nextMacroScope_32_);
lean_inc(v_env_31_);
lean_dec(v___x_30_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_65_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
lean_inc(v_currNamespace_29_);
v___x_42_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_31_, v_ext_22_, v_b_23_, v_kind_24_, v_currNamespace_29_);
v___x_43_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 5, v___x_43_);
lean_ctor_set(v___x_40_, 0, v___x_42_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_nextMacroScope_32_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_ngen_33_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_auxDeclNGen_34_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_traceState_35_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_64_, 6, v_messages_36_);
lean_ctor_set(v_reuseFailAlloc_64_, 7, v_infoState_37_);
lean_ctor_set(v_reuseFailAlloc_64_, 8, v_snapshotTasks_38_);
v___x_45_ = v_reuseFailAlloc_64_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v_mctx_48_; lean_object* v_zetaDeltaFVarIds_49_; lean_object* v_postponed_50_; lean_object* v_diag_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_62_; 
v___x_46_ = lean_st_ref_set(v___y_27_, v___x_45_);
v___x_47_ = lean_st_ref_take(v___y_25_);
v_mctx_48_ = lean_ctor_get(v___x_47_, 0);
v_zetaDeltaFVarIds_49_ = lean_ctor_get(v___x_47_, 2);
v_postponed_50_ = lean_ctor_get(v___x_47_, 3);
v_diag_51_ = lean_ctor_get(v___x_47_, 4);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; 
v_unused_63_ = lean_ctor_get(v___x_47_, 1);
lean_dec(v_unused_63_);
v___x_53_ = v___x_47_;
v_isShared_54_ = v_isSharedCheck_62_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_diag_51_);
lean_inc(v_postponed_50_);
lean_inc(v_zetaDeltaFVarIds_49_);
lean_inc(v_mctx_48_);
lean_dec(v___x_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_62_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_55_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_mctx_48_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v_zetaDeltaFVarIds_49_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v_postponed_50_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v_diag_51_);
v___x_57_ = v_reuseFailAlloc_61_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_st_ref_set(v___y_25_, v___x_57_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___boxed(lean_object* v_ext_67_, lean_object* v_b_68_, lean_object* v_kind_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v_kind_boxed_74_; lean_object* v_res_75_; 
v_kind_boxed_74_ = lean_unbox(v_kind_69_);
v_res_75_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_67_, v_b_68_, v_kind_boxed_74_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_00_u03c3_78_, lean_object* v_ext_79_, lean_object* v_b_80_, uint8_t v_kind_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_79_, v_b_80_, v_kind_81_, v___y_83_, v___y_84_, v___y_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___boxed(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_00_u03c3_90_, lean_object* v_ext_91_, lean_object* v_b_92_, lean_object* v_kind_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
uint8_t v_kind_boxed_99_; lean_object* v_res_100_; 
v_kind_boxed_99_ = lean_unbox(v_kind_93_);
v_res_100_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(v_00_u03b1_88_, v_00_u03b2_89_, v_00_u03c3_90_, v_ext_91_, v_b_92_, v_kind_boxed_99_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_env_108_; lean_object* v___x_109_; lean_object* v_mctx_110_; lean_object* v_lctx_111_; lean_object* v_options_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_107_);
v___x_109_ = lean_st_ref_get(v___y_103_);
v_mctx_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_mctx_110_);
lean_dec(v___x_109_);
v_lctx_111_ = lean_ctor_get(v___y_102_, 2);
v_options_112_ = lean_ctor_get(v___y_104_, 2);
lean_inc_ref(v_options_112_);
lean_inc_ref(v_lctx_111_);
v___x_113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_113_, 0, v_env_108_);
lean_ctor_set(v___x_113_, 1, v_mctx_110_);
lean_ctor_set(v___x_113_, 2, v_lctx_111_);
lean_ctor_set(v___x_113_, 3, v_options_112_);
v___x_114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_msgData_101_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3___boxed(lean_object* v_msgData_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(v_msgData_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 5);
v___x_130_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
lean_inc(v_ref_129_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_ref_129_);
lean_ctor_set(v___x_135_, 1, v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 1);
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg___boxed(lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(lean_object* v_ext_147_, uint8_t v_post_148_, uint8_t v_a_149_, uint8_t v_attrKind_150_, lean_object* v_prio_151_, lean_object* v_as_152_, size_t v_sz_153_, size_t v_i_154_, lean_object* v_b_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_lt(v_i_154_, v_sz_153_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_dec(v_prio_151_);
lean_dec_ref(v_ext_147_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v_b_155_);
return v___x_162_;
}
else
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_array_uget_borrowed(v_as_152_, v_i_154_);
lean_inc(v_prio_151_);
lean_inc(v_a_163_);
lean_inc_ref(v_ext_147_);
v___x_164_ = l_Lean_Meta_addSimpTheorem(v_ext_147_, v_a_163_, v_post_148_, v_a_149_, v_attrKind_150_, v_prio_151_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; size_t v___x_166_; size_t v___x_167_; 
lean_dec_ref(v___x_164_);
v___x_165_ = lean_box(0);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_154_, v___x_166_);
v_i_154_ = v___x_167_;
v_b_155_ = v___x_165_;
goto _start;
}
else
{
lean_dec(v_prio_151_);
lean_dec_ref(v_ext_147_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1___boxed(lean_object* v_ext_169_, lean_object* v_post_170_, lean_object* v_a_171_, lean_object* v_attrKind_172_, lean_object* v_prio_173_, lean_object* v_as_174_, lean_object* v_sz_175_, lean_object* v_i_176_, lean_object* v_b_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
uint8_t v_post_boxed_183_; uint8_t v_a_4556__boxed_184_; uint8_t v_attrKind_boxed_185_; size_t v_sz_boxed_186_; size_t v_i_boxed_187_; lean_object* v_res_188_; 
v_post_boxed_183_ = lean_unbox(v_post_170_);
v_a_4556__boxed_184_ = lean_unbox(v_a_171_);
v_attrKind_boxed_185_ = lean_unbox(v_attrKind_172_);
v_sz_boxed_186_ = lean_unbox_usize(v_sz_175_);
lean_dec(v_sz_175_);
v_i_boxed_187_ = lean_unbox_usize(v_i_176_);
lean_dec(v_i_176_);
v_res_188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_169_, v_post_boxed_183_, v_a_4556__boxed_184_, v_attrKind_boxed_185_, v_prio_173_, v_as_174_, v_sz_boxed_186_, v_i_boxed_187_, v_b_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec_ref(v_as_174_);
return v_res_188_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__2(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__1));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__4(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__3));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__6(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__5));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__7(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__6, &l_Lean_Meta_addDeclToUnfold___closed__6_once, _init_l_Lean_Meta_addDeclToUnfold___closed__6);
v___x_202_ = l_Lean_MessageData_note(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold(lean_object* v_ext_203_, lean_object* v_declName_204_, uint8_t v_post_205_, uint8_t v_inv_206_, lean_object* v_prio_207_, uint8_t v_attrKind_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; lean_object* v_env_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; 
v___x_214_ = lean_st_ref_get(v_a_212_);
v_env_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_env_215_);
lean_dec(v___x_214_);
lean_inc(v_declName_204_);
v___x_216_ = l_Lean_getOriginalConstKind_x3f(v_env_215_, v_declName_204_);
v___x_217_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__0));
v___x_218_ = l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
if (v___x_218_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_prio_207_);
lean_dec(v_declName_204_);
lean_dec_ref(v_ext_203_);
v___x_312_ = lean_box(v___x_218_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
else
{
if (v_inv_206_ == 0)
{
v___y_220_ = v_a_209_;
v___y_221_ = v_a_210_;
v___y_222_ = v_a_211_;
v___y_223_ = v_a_212_;
goto v___jp_219_;
}
else
{
lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_prio_207_);
lean_dec_ref(v_ext_203_);
v___x_314_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__2, &l_Lean_Meta_addDeclToUnfold___closed__2_once, _init_l_Lean_Meta_addDeclToUnfold___closed__2);
v___x_315_ = 0;
v___x_316_ = l_Lean_MessageData_ofConstName(v_declName_204_, v___x_315_);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__4, &l_Lean_Meta_addDeclToUnfold___closed__4_once, _init_l_Lean_Meta_addDeclToUnfold___closed__4);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__7, &l_Lean_Meta_addDeclToUnfold___closed__7_once, _init_l_Lean_Meta_addDeclToUnfold___closed__7);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_321_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
v___jp_219_:
{
lean_object* v___x_224_; 
lean_inc(v_declName_204_);
v___x_224_ = l_Lean_Meta_Simp_ignoreEquations(v_declName_204_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_311_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_311_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_311_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_311_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
uint8_t v___x_229_; 
v___x_229_ = lean_unbox(v_a_225_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_inc(v_declName_204_);
v___x_230_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_204_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
if (lean_obj_tag(v_a_231_) == 1)
{
lean_object* v_val_232_; lean_object* v___x_233_; size_t v_sz_234_; size_t v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_227_);
v_val_232_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_val_232_);
lean_dec_ref(v_a_231_);
v___x_233_ = lean_box(0);
v_sz_234_ = lean_array_size(v_val_232_);
v___x_235_ = ((size_t)0ULL);
v___x_236_ = lean_unbox(v_a_225_);
lean_dec(v_a_225_);
lean_inc_ref(v_ext_203_);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_203_, v_post_205_, v___x_236_, v_attrKind_208_, v_prio_207_, v_val_232_, v_sz_234_, v___x_235_, v___x_233_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v___x_237_);
lean_inc(v_declName_204_);
v___x_238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_238_, 0, v_declName_204_);
lean_ctor_set(v___x_238_, 1, v_val_232_);
lean_inc_ref(v_ext_203_);
v___x_239_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_203_, v___x_238_, v_attrKind_208_, v___y_221_, v___y_222_, v___y_223_);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_239_, 0);
lean_dec(v_unused_268_);
v___x_241_ = v___x_239_;
v_isShared_242_ = v_isSharedCheck_267_;
goto v_resetjp_240_;
}
else
{
lean_dec(v___x_239_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_267_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; 
lean_inc(v_declName_204_);
v___x_243_ = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(v_declName_204_, v___y_223_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_266_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_266_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_266_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_266_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; 
v___x_248_ = lean_unbox(v_a_244_);
lean_dec(v_a_244_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_del_object(v___x_241_);
lean_dec(v_declName_204_);
lean_dec_ref(v_ext_203_);
v___x_249_ = lean_box(v___x_218_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_249_);
v___x_251_ = v___x_246_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_254_; 
lean_del_object(v___x_246_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 0, v_declName_204_);
v___x_254_ = v___x_241_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_declName_204_);
v___x_254_ = v_reuseFailAlloc_265_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v___x_255_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_203_, v___x_254_, v_attrKind_208_, v___y_221_, v___y_222_, v___y_223_);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_264_);
v___x_257_ = v___x_255_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_dec(v___x_255_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_box(v___x_218_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_241_);
lean_dec(v_declName_204_);
lean_dec_ref(v_ext_203_);
return v___x_243_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_val_232_);
lean_dec(v_declName_204_);
lean_dec_ref(v_ext_203_);
v_a_269_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_237_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_237_);
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
lean_object* v___x_278_; 
lean_dec(v_a_231_);
lean_dec(v_a_225_);
lean_dec(v_prio_207_);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 1);
lean_ctor_set(v___x_227_, 0, v_declName_204_);
v___x_278_ = v___x_227_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_declName_204_);
v___x_278_ = v_reuseFailAlloc_289_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v___x_279_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_203_, v___x_278_, v_attrKind_208_, v___y_221_, v___y_222_, v___y_223_);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_279_, 0);
lean_dec(v_unused_288_);
v___x_281_ = v___x_279_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_dec(v___x_279_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_box(v___x_218_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_del_object(v___x_227_);
lean_dec(v_a_225_);
lean_dec(v_prio_207_);
lean_dec(v_declName_204_);
lean_dec_ref(v_ext_203_);
v_a_290_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_230_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_230_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v_a_225_);
lean_dec(v_prio_207_);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 1);
lean_ctor_set(v___x_227_, 0, v_declName_204_);
v___x_299_ = v___x_227_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_declName_204_);
v___x_299_ = v_reuseFailAlloc_310_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v___x_300_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_203_, v___x_299_, v_attrKind_208_, v___y_221_, v___y_222_, v___y_223_);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_300_, 0);
lean_dec(v_unused_309_);
v___x_302_ = v___x_300_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_dec(v___x_300_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_box(v___x_218_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
}
else
{
lean_dec(v_prio_207_);
lean_dec(v_declName_204_);
lean_dec_ref(v_ext_203_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold___boxed(lean_object* v_ext_331_, lean_object* v_declName_332_, lean_object* v_post_333_, lean_object* v_inv_334_, lean_object* v_prio_335_, lean_object* v_attrKind_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
uint8_t v_post_boxed_342_; uint8_t v_inv_boxed_343_; uint8_t v_attrKind_boxed_344_; lean_object* v_res_345_; 
v_post_boxed_342_ = lean_unbox(v_post_333_);
v_inv_boxed_343_ = lean_unbox(v_inv_334_);
v_attrKind_boxed_344_ = lean_unbox(v_attrKind_336_);
v_res_345_ = l_Lean_Meta_addDeclToUnfold(v_ext_331_, v_declName_332_, v_post_boxed_342_, v_inv_boxed_343_, v_prio_335_, v_attrKind_boxed_344_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(lean_object* v_00_u03b1_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___boxed(lean_object* v_00_u03b1_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(v_00_u03b1_354_, v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__10));
v___x_389_ = l_Lean_mkAtom(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__12, &l_Lean_Meta_mkSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12);
v___x_391_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_392_ = lean_array_push(v___x_391_, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__17));
v___x_402_ = l_Lean_mkAtom(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__18, &l_Lean_Meta_mkSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18);
v___x_404_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_405_ = lean_array_push(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__19, &l_Lean_Meta_mkSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19);
v___x_407_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__16));
v___x_408_ = lean_box(2);
v___x_409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__20, &l_Lean_Meta_mkSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20);
v___x_411_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__13, &l_Lean_Meta_mkSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13);
v___x_412_ = lean_array_push(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__21, &l_Lean_Meta_mkSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21);
v___x_414_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__11));
v___x_415_ = lean_box(2);
v___x_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__22, &l_Lean_Meta_mkSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22);
v___x_418_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_419_ = lean_array_push(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__23, &l_Lean_Meta_mkSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23);
v___x_421_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__9));
v___x_422_ = lean_box(2);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__24, &l_Lean_Meta_mkSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24);
v___x_425_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_426_ = lean_array_push(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__25, &l_Lean_Meta_mkSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25);
v___x_428_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__7));
v___x_429_ = lean_box(2);
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_427_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__26, &l_Lean_Meta_mkSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26);
v___x_432_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__27, &l_Lean_Meta_mkSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27);
v___x_435_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__4));
v___x_436_ = lean_box(2);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set(v___x_444_, 3, v___x_443_);
lean_ctor_set(v___x_444_, 4, v___x_442_);
lean_ctor_set(v___x_444_, 5, v___x_442_);
lean_ctor_set(v___x_444_, 6, v___x_442_);
lean_ctor_set(v___x_444_, 7, v___x_442_);
lean_ctor_set(v___x_444_, 8, v___x_442_);
lean_ctor_set(v___x_444_, 9, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_453_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set(v___x_453_, 3, v___x_449_);
lean_ctor_set_usize(v___x_453_, 4, v___x_448_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_box(1);
v___x_455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14));
v___x_472_ = l_Lean_stringToMessageData(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_msg_479_, lean_object* v_declHint_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; lean_object* v_env_484_; uint8_t v___x_485_; 
v___x_483_ = lean_st_ref_get(v___y_481_);
v_env_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_env_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Lean_Name_isAnonymous(v_declHint_480_);
if (v___x_485_ == 0)
{
uint8_t v_isExporting_486_; 
v_isExporting_486_ = lean_ctor_get_uint8(v_env_484_, sizeof(void*)*8);
if (v_isExporting_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_480_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_msg_479_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
lean_inc_ref(v_env_484_);
v___x_488_ = l_Lean_Environment_setExporting(v_env_484_, v___x_485_);
lean_inc(v_declHint_480_);
lean_inc_ref(v___x_488_);
v___x_489_ = l_Lean_Environment_contains(v___x_488_, v_declHint_480_, v_isExporting_486_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v___x_488_);
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_480_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_msg_479_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_c_496_; lean_object* v___x_497_; 
v___x_491_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
v___x_492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5);
v___x_493_ = l_Lean_Options_empty;
v___x_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_494_, 0, v___x_488_);
lean_ctor_set(v___x_494_, 1, v___x_491_);
lean_ctor_set(v___x_494_, 2, v___x_492_);
lean_ctor_set(v___x_494_, 3, v___x_493_);
lean_inc(v_declHint_480_);
v___x_495_ = l_Lean_MessageData_ofConstName(v_declHint_480_, v___x_485_);
v_c_496_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_496_, 0, v___x_494_);
lean_ctor_set(v_c_496_, 1, v___x_495_);
v___x_497_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_484_, v_declHint_480_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_480_);
v___x_498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_c_496_);
v___x_500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_MessageData_note(v___x_501_);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v_msg_479_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_540_; 
v_val_505_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_540_ == 0)
{
v___x_507_ = v___x_497_;
v_isShared_508_ = v_isSharedCheck_540_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v___x_497_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_540_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_mod_512_; uint8_t v___x_513_; 
v___x_509_ = lean_box(0);
v___x_510_ = l_Lean_Environment_header(v_env_484_);
lean_dec_ref(v_env_484_);
v___x_511_ = l_Lean_EnvironmentHeader_moduleNames(v___x_510_);
v_mod_512_ = lean_array_get(v___x_509_, v___x_511_, v_val_505_);
lean_dec(v_val_505_);
lean_dec_ref(v___x_511_);
v___x_513_ = l_Lean_isPrivateName(v_declHint_480_);
lean_dec(v_declHint_480_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_514_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_c_496_);
v___x_516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_MessageData_ofName(v_mod_512_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_MessageData_note(v___x_521_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v_msg_479_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_523_);
v___x_525_ = v___x_507_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_527_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_c_496_);
v___x_529_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_MessageData_ofName(v_mod_512_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_MessageData_note(v___x_534_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v_msg_479_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_536_);
v___x_538_ = v___x_507_;
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
}
}
}
else
{
lean_object* v___x_541_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_480_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_msg_479_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_msg_542_, lean_object* v_declHint_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_542_, v_declHint_543_, v___y_544_);
lean_dec(v___y_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_msg_547_, lean_object* v_declHint_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_564_; 
v___x_554_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_547_, v_declHint_548_, v___y_552_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = l_Lean_unknownIdentifierMessageTag;
v___x_560_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msg_565_, lean_object* v_declHint_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_565_, v_declHint_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_ref_573_, lean_object* v_msg_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_fileName_580_; lean_object* v_fileMap_581_; lean_object* v_options_582_; lean_object* v_currRecDepth_583_; lean_object* v_maxRecDepth_584_; lean_object* v_ref_585_; lean_object* v_currNamespace_586_; lean_object* v_openDecls_587_; lean_object* v_initHeartbeats_588_; lean_object* v_maxHeartbeats_589_; lean_object* v_quotContext_590_; lean_object* v_currMacroScope_591_; uint8_t v_diag_592_; lean_object* v_cancelTk_x3f_593_; uint8_t v_suppressElabErrors_594_; lean_object* v_inheritedTraceOptions_595_; lean_object* v_ref_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_fileName_580_ = lean_ctor_get(v___y_577_, 0);
v_fileMap_581_ = lean_ctor_get(v___y_577_, 1);
v_options_582_ = lean_ctor_get(v___y_577_, 2);
v_currRecDepth_583_ = lean_ctor_get(v___y_577_, 3);
v_maxRecDepth_584_ = lean_ctor_get(v___y_577_, 4);
v_ref_585_ = lean_ctor_get(v___y_577_, 5);
v_currNamespace_586_ = lean_ctor_get(v___y_577_, 6);
v_openDecls_587_ = lean_ctor_get(v___y_577_, 7);
v_initHeartbeats_588_ = lean_ctor_get(v___y_577_, 8);
v_maxHeartbeats_589_ = lean_ctor_get(v___y_577_, 9);
v_quotContext_590_ = lean_ctor_get(v___y_577_, 10);
v_currMacroScope_591_ = lean_ctor_get(v___y_577_, 11);
v_diag_592_ = lean_ctor_get_uint8(v___y_577_, sizeof(void*)*14);
v_cancelTk_x3f_593_ = lean_ctor_get(v___y_577_, 12);
v_suppressElabErrors_594_ = lean_ctor_get_uint8(v___y_577_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_595_ = lean_ctor_get(v___y_577_, 13);
v_ref_596_ = l_Lean_replaceRef(v_ref_573_, v_ref_585_);
lean_inc_ref(v_inheritedTraceOptions_595_);
lean_inc(v_cancelTk_x3f_593_);
lean_inc(v_currMacroScope_591_);
lean_inc(v_quotContext_590_);
lean_inc(v_maxHeartbeats_589_);
lean_inc(v_initHeartbeats_588_);
lean_inc(v_openDecls_587_);
lean_inc(v_currNamespace_586_);
lean_inc(v_maxRecDepth_584_);
lean_inc(v_currRecDepth_583_);
lean_inc_ref(v_options_582_);
lean_inc_ref(v_fileMap_581_);
lean_inc_ref(v_fileName_580_);
v___x_597_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_597_, 0, v_fileName_580_);
lean_ctor_set(v___x_597_, 1, v_fileMap_581_);
lean_ctor_set(v___x_597_, 2, v_options_582_);
lean_ctor_set(v___x_597_, 3, v_currRecDepth_583_);
lean_ctor_set(v___x_597_, 4, v_maxRecDepth_584_);
lean_ctor_set(v___x_597_, 5, v_ref_596_);
lean_ctor_set(v___x_597_, 6, v_currNamespace_586_);
lean_ctor_set(v___x_597_, 7, v_openDecls_587_);
lean_ctor_set(v___x_597_, 8, v_initHeartbeats_588_);
lean_ctor_set(v___x_597_, 9, v_maxHeartbeats_589_);
lean_ctor_set(v___x_597_, 10, v_quotContext_590_);
lean_ctor_set(v___x_597_, 11, v_currMacroScope_591_);
lean_ctor_set(v___x_597_, 12, v_cancelTk_x3f_593_);
lean_ctor_set(v___x_597_, 13, v_inheritedTraceOptions_595_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*14, v_diag_592_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*14 + 1, v_suppressElabErrors_594_);
v___x_598_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_574_, v___y_575_, v___y_576_, v___x_597_, v___y_578_);
lean_dec_ref(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_ref_599_, lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_599_, v_msg_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v_ref_599_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_607_, lean_object* v_msg_608_, lean_object* v_declHint_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v_a_616_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_608_, v_declHint_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref(v___x_615_);
v___x_617_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_607_, v_a_616_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_618_, lean_object* v_msg_619_, lean_object* v_declHint_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_618_, v_msg_619_, v_declHint_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v_ref_618_);
return v_res_626_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_633_, lean_object* v_constName_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_640_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_641_ = 0;
lean_inc(v_constName_634_);
v___x_642_ = l_Lean_MessageData_ofConstName(v_constName_634_, v___x_641_);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_640_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_633_, v___x_645_, v_constName_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_647_, lean_object* v_constName_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_647_, v_constName_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v_ref_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object* v_constName_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_ref_661_; lean_object* v___x_662_; 
v_ref_661_ = lean_ctor_get(v___y_658_, 5);
v___x_662_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_661_, v_constName_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_constName_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object* v_constName_670_, uint8_t v_skipRealize_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; lean_object* v_env_678_; lean_object* v___x_679_; 
v___x_677_ = lean_st_ref_get(v___y_675_);
v_env_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_env_678_);
lean_dec(v___x_677_);
lean_inc(v_constName_670_);
v___x_679_ = l_Lean_Environment_findAsync_x3f(v_env_678_, v_constName_670_, v_skipRealize_671_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_670_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v___x_680_;
}
else
{
lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec(v_constName_670_);
v_val_681_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_679_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_dec(v___x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 0);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_val_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object* v_constName_689_, lean_object* v_skipRealize_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
uint8_t v_skipRealize_boxed_696_; lean_object* v_res_697_; 
v_skipRealize_boxed_696_ = lean_unbox(v_skipRealize_690_);
v_res_697_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_constName_689_, v_skipRealize_boxed_696_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_697_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__0));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__2));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__4));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__5, &l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5);
v___x_708_ = l_Lean_MessageData_note(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__7, &l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_box(1);
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_714_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_712_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_ctor_set(v___x_720_, 2, v___x_719_);
lean_ctor_set(v___x_720_, 3, v___x_719_);
lean_ctor_set(v___x_720_, 4, v___x_718_);
lean_ctor_set(v___x_720_, 5, v___x_718_);
lean_ctor_set(v___x_720_, 6, v___x_718_);
lean_ctor_set(v___x_720_, 7, v___x_718_);
lean_ctor_set(v___x_720_, 8, v___x_718_);
lean_ctor_set(v___x_720_, 9, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_722_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
lean_ctor_set(v___x_722_, 4, v___x_721_);
lean_ctor_set(v___x_722_, 5, v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
lean_ctor_set(v___x_724_, 4, v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__14(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__13, &l_Lean_Meta_mkSimpAttr___lam__0___closed__13_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13);
v___x_726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_727_ = lean_box(1);
v___x_728_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__12, &l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12);
v___x_729_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__11, &l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11);
v___x_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_727_);
lean_ctor_set(v___x_730_, 3, v___x_726_);
lean_ctor_set(v___x_730_, 4, v___x_725_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object* v_ext_737_, lean_object* v_attrName_738_, lean_object* v_declName_739_, lean_object* v_stx_740_, uint8_t v_attrKind_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; uint8_t v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_820_; lean_object* v___x_878_; 
lean_inc(v_declName_739_);
v___x_878_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_739_, v___y_743_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
v___x_880_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec_ref(v___x_878_);
v___x_881_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_739_, v___y_743_);
v___y_820_ = v___x_881_;
goto v___jp_819_;
}
else
{
v___y_820_ = v___x_878_;
goto v___jp_819_;
}
}
else
{
v___y_820_ = v___x_878_;
goto v___jp_819_;
}
v___jp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_st_ref_get(v___y_747_);
lean_dec(v___y_747_);
lean_dec(v___x_748_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___y_746_);
return v___x_749_;
}
v___jp_750_:
{
if (lean_obj_tag(v___y_753_) == 0)
{
lean_dec_ref(v___y_753_);
v___y_746_ = v___y_751_;
v___y_747_ = v___y_752_;
goto v___jp_745_;
}
else
{
lean_dec(v___y_752_);
return v___y_753_;
}
}
v___jp_754_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(3u);
v___x_763_ = l_Lean_Syntax_getArg(v_stx_740_, v___x_762_);
lean_dec(v_stx_740_);
v___x_764_ = l_Lean_getAttrParamOptPrio(v___x_763_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_sig_766_; lean_object* v___x_767_; lean_object* v_type_768_; lean_object* v___x_769_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
v_sig_766_ = lean_ctor_get(v___y_755_, 1);
lean_inc_ref(v_sig_766_);
lean_dec_ref(v___y_755_);
v___x_767_ = lean_task_get_own(v_sig_766_);
v_type_768_ = lean_ctor_get(v___x_767_, 2);
lean_inc_ref(v_type_768_);
lean_dec(v___x_767_);
v___x_769_ = l_Lean_Meta_isProp(v_type_768_, v___y_760_, v___y_758_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; uint8_t v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v___x_771_ = lean_unbox(v_a_770_);
lean_dec(v_a_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_inc(v_declName_739_);
v___x_772_ = l_Lean_Meta_addDeclToUnfold(v_ext_737_, v_declName_739_, v___y_756_, v___y_761_, v_a_765_, v_attrKind_741_, v___y_760_, v___y_758_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; uint8_t v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_774_ = lean_unbox(v_a_773_);
lean_dec(v_a_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_775_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__1, &l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1);
v___x_776_ = l_Lean_MessageData_ofConstName(v_declName_739_, v___y_759_);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__6, &l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_781_, v___y_760_, v___y_758_, v___y_742_, v___y_743_);
lean_dec_ref(v___y_760_);
v___y_751_ = v___y_757_;
v___y_752_ = v___y_758_;
v___y_753_ = v___x_782_;
goto v___jp_750_;
}
else
{
lean_dec_ref(v___y_760_);
lean_dec(v_declName_739_);
v___y_746_ = v___y_757_;
v___y_747_ = v___y_758_;
goto v___jp_745_;
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___y_760_);
lean_dec(v___y_758_);
lean_dec(v_declName_739_);
v_a_783_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_772_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_772_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_addSimpTheorem(v_ext_737_, v_declName_739_, v___y_756_, v___y_761_, v_attrKind_741_, v_a_765_, v___y_760_, v___y_758_, v___y_742_, v___y_743_);
lean_dec_ref(v___y_760_);
v___y_751_ = v___y_757_;
v___y_752_ = v___y_758_;
v___y_753_ = v___x_791_;
goto v___jp_750_;
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_a_765_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_758_);
lean_dec(v_declName_739_);
lean_dec_ref(v_ext_737_);
v_a_792_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_769_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_769_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___y_760_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_755_);
lean_dec(v_declName_739_);
lean_dec_ref(v_ext_737_);
v_a_800_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_764_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_764_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
v___jp_808_:
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_816_ = lean_unsigned_to_nat(2u);
v___x_817_ = l_Lean_Syntax_getArg(v_stx_740_, v___x_816_);
v___x_818_ = l_Lean_Syntax_isNone(v___x_817_);
lean_dec(v___x_817_);
if (v___x_818_ == 0)
{
v___y_755_ = v___y_809_;
v___y_756_ = v___y_815_;
v___y_757_ = v___y_810_;
v___y_758_ = v___y_811_;
v___y_759_ = v___y_813_;
v___y_760_ = v___y_814_;
v___y_761_ = v___y_812_;
goto v___jp_754_;
}
else
{
v___y_755_ = v___y_809_;
v___y_756_ = v___y_815_;
v___y_757_ = v___y_810_;
v___y_758_ = v___y_811_;
v___y_759_ = v___y_813_;
v___y_760_ = v___y_814_;
v___y_761_ = v___y_813_;
goto v___jp_754_;
}
}
v___jp_819_:
{
if (lean_obj_tag(v___y_820_) == 0)
{
lean_object* v_a_821_; uint8_t v___x_822_; 
v_a_821_ = lean_ctor_get(v___y_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___y_820_);
v___x_822_ = lean_unbox(v_a_821_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; uint8_t v___x_824_; uint8_t v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; uint8_t v___x_829_; uint8_t v___x_830_; uint8_t v___x_831_; uint8_t v___x_832_; uint8_t v___x_833_; uint64_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; uint8_t v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; 
lean_dec(v_attrName_738_);
v___x_823_ = 1;
v___x_824_ = 1;
v___x_825_ = 0;
v___x_826_ = 2;
v___x_827_ = lean_alloc_ctor(0, 0, 19);
v___x_828_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_827_, 0, v___x_828_);
v___x_829_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_827_, 1, v___x_829_);
v___x_830_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_827_, 2, v___x_830_);
v___x_831_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_827_, 3, v___x_831_);
v___x_832_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_827_, 4, v___x_832_);
lean_ctor_set_uint8(v___x_827_, 5, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 6, v___x_823_);
v___x_833_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_827_, 7, v___x_833_);
lean_ctor_set_uint8(v___x_827_, 8, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 9, v___x_824_);
lean_ctor_set_uint8(v___x_827_, 10, v___x_825_);
lean_ctor_set_uint8(v___x_827_, 11, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 12, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 13, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 14, v___x_826_);
lean_ctor_set_uint8(v___x_827_, 15, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 16, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 17, v___x_823_);
lean_ctor_set_uint8(v___x_827_, 18, v___x_823_);
v___x_834_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_827_);
v___x_835_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_835_, 0, v___x_827_);
lean_ctor_set_uint64(v___x_835_, sizeof(void*)*1, v___x_834_);
v___x_836_ = lean_box(1);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__9, &l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9);
v___x_839_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__10));
v___x_840_ = lean_box(0);
v___x_841_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_841_, 0, v___x_835_);
lean_ctor_set(v___x_841_, 1, v___x_836_);
lean_ctor_set(v___x_841_, 2, v___x_838_);
lean_ctor_set(v___x_841_, 3, v___x_839_);
lean_ctor_set(v___x_841_, 4, v___x_840_);
lean_ctor_set(v___x_841_, 5, v___x_837_);
lean_ctor_set(v___x_841_, 6, v___x_840_);
v___x_842_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7, v___x_842_);
v___x_843_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 1, v___x_843_);
v___x_844_ = lean_unbox(v_a_821_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 2, v___x_844_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 3, v___x_823_);
v___x_845_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__14, &l_Lean_Meta_mkSimpAttr___lam__0___closed__14_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__14);
v___x_846_ = lean_st_mk_ref(v___x_845_);
v___x_847_ = lean_unbox(v_a_821_);
lean_inc(v_declName_739_);
v___x_848_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_declName_739_, v___x_847_, v___x_841_, v___x_846_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref(v___x_848_);
v___x_850_ = lean_box(0);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = l_Lean_Syntax_getArg(v_stx_740_, v___x_851_);
v___x_853_ = l_Lean_Syntax_isNone(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_854_ = l_Lean_Syntax_getArg(v___x_852_, v___x_837_);
lean_dec(v___x_852_);
v___x_855_ = l_Lean_Syntax_getKind(v___x_854_);
v___x_856_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__16));
v___x_857_ = lean_name_eq(v___x_855_, v___x_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_unbox(v_a_821_);
lean_dec(v_a_821_);
v___y_809_ = v_a_849_;
v___y_810_ = v___x_850_;
v___y_811_ = v___x_846_;
v___y_812_ = v___x_823_;
v___y_813_ = v___x_858_;
v___y_814_ = v___x_841_;
v___y_815_ = v___x_857_;
goto v___jp_808_;
}
else
{
uint8_t v___x_859_; 
lean_dec(v___x_852_);
v___x_859_ = lean_unbox(v_a_821_);
lean_dec(v_a_821_);
v___y_809_ = v_a_849_;
v___y_810_ = v___x_850_;
v___y_811_ = v___x_846_;
v___y_812_ = v___x_823_;
v___y_813_ = v___x_859_;
v___y_814_ = v___x_841_;
v___y_815_ = v___x_823_;
goto v___jp_808_;
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v___x_846_);
lean_dec_ref(v___x_841_);
lean_dec(v_a_821_);
lean_dec(v_stx_740_);
lean_dec(v_declName_739_);
lean_dec_ref(v_ext_737_);
v_a_860_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_848_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_848_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v_a_821_);
lean_dec_ref(v_ext_737_);
v___x_868_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_738_);
v___x_869_ = l_Lean_Attribute_add(v_declName_739_, v___x_868_, v_stx_740_, v_attrKind_741_, v___y_742_, v___y_743_);
return v___x_869_;
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_stx_740_);
lean_dec(v_declName_739_);
lean_dec(v_attrName_738_);
lean_dec_ref(v_ext_737_);
v_a_870_ = lean_ctor_get(v___y_820_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___y_820_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___y_820_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___y_820_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object* v_ext_882_, lean_object* v_attrName_883_, lean_object* v_declName_884_, lean_object* v_stx_885_, lean_object* v_attrKind_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_attrKind_boxed_890_; lean_object* v_res_891_; 
v_attrKind_boxed_890_ = lean_unbox(v_attrKind_886_);
v_res_891_ = l_Lean_Meta_mkSimpAttr___lam__0(v_ext_882_, v_attrName_883_, v_declName_884_, v_stx_885_, v_attrKind_boxed_890_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object* v_a_892_, lean_object* v_x_893_){
_start:
{
lean_inc_ref(v_a_892_);
return v_a_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Meta_mkSimpAttr___lam__1(v_a_894_, v_x_895_);
lean_dec_ref(v_x_895_);
lean_dec_ref(v_a_894_);
return v_res_896_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_keys_897_, lean_object* v_i_898_, lean_object* v_k_899_){
_start:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_array_get_size(v_keys_897_);
v___x_901_ = lean_nat_dec_lt(v_i_898_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec(v_i_898_);
return v___x_901_;
}
else
{
lean_object* v_k_x27_902_; uint8_t v___x_903_; 
v_k_x27_902_ = lean_array_fget_borrowed(v_keys_897_, v_i_898_);
v___x_903_ = lean_name_eq(v_k_899_, v_k_x27_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_add(v_i_898_, v___x_904_);
lean_dec(v_i_898_);
v_i_898_ = v___x_905_;
goto _start;
}
else
{
lean_dec(v_i_898_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_keys_907_, lean_object* v_i_908_, lean_object* v_k_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_907_, v_i_908_, v_k_909_);
lean_dec(v_k_909_);
lean_dec_ref(v_keys_907_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; 
v___x_912_ = ((size_t)5ULL);
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_shift_left(v___x_913_, v___x_912_);
return v___x_914_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; 
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_917_ = lean_usize_sub(v___x_916_, v___x_915_);
return v___x_917_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(lean_object* v_x_918_, size_t v_x_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_es_921_; lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; lean_object* v_j_926_; lean_object* v___x_927_; 
v_es_921_ = lean_ctor_get(v_x_918_, 0);
v___x_922_ = lean_box(2);
v___x_923_ = ((size_t)5ULL);
v___x_924_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1);
v___x_925_ = lean_usize_land(v_x_919_, v___x_924_);
v_j_926_ = lean_usize_to_nat(v___x_925_);
v___x_927_ = lean_array_get_borrowed(v___x_922_, v_es_921_, v_j_926_);
lean_dec(v_j_926_);
switch(lean_obj_tag(v___x_927_))
{
case 0:
{
lean_object* v_key_928_; uint8_t v___x_929_; 
v_key_928_ = lean_ctor_get(v___x_927_, 0);
v___x_929_ = lean_name_eq(v_x_920_, v_key_928_);
return v___x_929_;
}
case 1:
{
lean_object* v_node_930_; size_t v___x_931_; 
v_node_930_ = lean_ctor_get(v___x_927_, 0);
v___x_931_ = lean_usize_shift_right(v_x_919_, v___x_923_);
v_x_918_ = v_node_930_;
v_x_919_ = v___x_931_;
goto _start;
}
default: 
{
uint8_t v___x_933_; 
v___x_933_ = 0;
return v___x_933_;
}
}
}
else
{
lean_object* v_ks_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_ks_934_ = lean_ctor_get(v_x_918_, 0);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_ks_934_, v___x_935_, v_x_920_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
size_t v_x_9279__boxed_940_; uint8_t v_res_941_; lean_object* v_r_942_; 
v_x_9279__boxed_940_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_res_941_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_937_, v_x_9279__boxed_940_, v_x_939_);
lean_dec(v_x_939_);
lean_dec_ref(v_x_937_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_943_; uint64_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(1723u);
v___x_944_ = lean_uint64_of_nat(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
uint64_t v___y_948_; 
if (lean_obj_tag(v_x_946_) == 0)
{
uint64_t v___x_951_; 
v___x_951_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0);
v___y_948_ = v___x_951_;
goto v___jp_947_;
}
else
{
uint64_t v_hash_952_; 
v_hash_952_ = lean_ctor_get_uint64(v_x_946_, sizeof(void*)*2);
v___y_948_ = v_hash_952_;
goto v___jp_947_;
}
v___jp_947_:
{
size_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_uint64_to_usize(v___y_948_);
v___x_950_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_945_, v___x_949_, v_x_946_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___boxed(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_953_, v_x_954_);
lean_dec(v_x_954_);
lean_dec_ref(v_x_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_msgData_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_env_962_; lean_object* v_options_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_961_ = lean_st_ref_get(v___y_959_);
v_env_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_961_);
v_options_963_ = lean_ctor_get(v___y_958_, 2);
v___x_964_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
v___x_965_ = lean_unsigned_to_nat(32u);
v___x_966_ = lean_mk_empty_array_with_capacity(v___x_965_);
lean_dec_ref(v___x_966_);
v___x_967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5);
lean_inc_ref(v_options_963_);
v___x_968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_968_, 0, v_env_962_);
lean_ctor_set(v___x_968_, 1, v___x_964_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
lean_ctor_set(v___x_968_, 3, v_options_963_);
v___x_969_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_msgData_957_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_msgData_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v_msgData_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(uint8_t v___y_983_, uint8_t v_suppressElabErrors_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_985_) == 1)
{
lean_object* v_pre_986_; 
v_pre_986_ = lean_ctor_get(v_x_985_, 0);
switch(lean_obj_tag(v_pre_986_))
{
case 1:
{
lean_object* v_pre_987_; 
v_pre_987_ = lean_ctor_get(v_pre_986_, 0);
switch(lean_obj_tag(v_pre_987_))
{
case 0:
{
lean_object* v_str_988_; lean_object* v_str_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_str_988_ = lean_ctor_get(v_x_985_, 1);
v_str_989_ = lean_ctor_get(v_pre_986_, 1);
v___x_990_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0));
v___x_991_ = lean_string_dec_eq(v_str_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__2));
v___x_993_ = lean_string_dec_eq(v_str_989_, v___x_992_);
if (v___x_993_ == 0)
{
return v___y_983_;
}
else
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1));
v___x_995_ = lean_string_dec_eq(v_str_988_, v___x_994_);
if (v___x_995_ == 0)
{
return v___y_983_;
}
else
{
return v_suppressElabErrors_984_;
}
}
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2));
v___x_997_ = lean_string_dec_eq(v_str_988_, v___x_996_);
if (v___x_997_ == 0)
{
return v___y_983_;
}
else
{
return v_suppressElabErrors_984_;
}
}
}
case 1:
{
lean_object* v_pre_998_; 
v_pre_998_ = lean_ctor_get(v_pre_987_, 0);
if (lean_obj_tag(v_pre_998_) == 0)
{
lean_object* v_str_999_; lean_object* v_str_1000_; lean_object* v_str_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_str_999_ = lean_ctor_get(v_x_985_, 1);
v_str_1000_ = lean_ctor_get(v_pre_986_, 1);
v_str_1001_ = lean_ctor_get(v_pre_987_, 1);
v___x_1002_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3));
v___x_1003_ = lean_string_dec_eq(v_str_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
return v___y_983_;
}
else
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4));
v___x_1005_ = lean_string_dec_eq(v_str_1000_, v___x_1004_);
if (v___x_1005_ == 0)
{
return v___y_983_;
}
else
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5));
v___x_1007_ = lean_string_dec_eq(v_str_999_, v___x_1006_);
if (v___x_1007_ == 0)
{
return v___y_983_;
}
else
{
return v_suppressElabErrors_984_;
}
}
}
}
else
{
return v___y_983_;
}
}
default: 
{
return v___y_983_;
}
}
}
case 0:
{
lean_object* v_str_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_str_1008_ = lean_ctor_get(v_x_985_, 1);
v___x_1009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6));
v___x_1010_ = lean_string_dec_eq(v_str_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
return v___y_983_;
}
else
{
return v_suppressElabErrors_984_;
}
}
default: 
{
return v___y_983_;
}
}
}
else
{
return v___y_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(lean_object* v___y_1011_, lean_object* v_suppressElabErrors_1012_, lean_object* v_x_1013_){
_start:
{
uint8_t v___y_9422__boxed_1014_; uint8_t v_suppressElabErrors_boxed_1015_; uint8_t v_res_1016_; lean_object* v_r_1017_; 
v___y_9422__boxed_1014_ = lean_unbox(v___y_1011_);
v_suppressElabErrors_boxed_1015_ = lean_unbox(v_suppressElabErrors_1012_);
v_res_1016_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(v___y_9422__boxed_1014_, v_suppressElabErrors_boxed_1015_, v_x_1013_);
lean_dec(v_x_1013_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(lean_object* v_opts_1018_, lean_object* v_opt_1019_){
_start:
{
lean_object* v_name_1020_; lean_object* v_defValue_1021_; lean_object* v_map_1022_; lean_object* v___x_1023_; 
v_name_1020_ = lean_ctor_get(v_opt_1019_, 0);
v_defValue_1021_ = lean_ctor_get(v_opt_1019_, 1);
v_map_1022_ = lean_ctor_get(v_opts_1018_, 0);
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1022_, v_name_1020_);
if (lean_obj_tag(v___x_1023_) == 0)
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_unbox(v_defValue_1021_);
return v___x_1024_;
}
else
{
lean_object* v_val_1025_; 
v_val_1025_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1025_);
lean_dec_ref(v___x_1023_);
if (lean_obj_tag(v_val_1025_) == 1)
{
uint8_t v_v_1026_; 
v_v_1026_ = lean_ctor_get_uint8(v_val_1025_, 0);
lean_dec_ref(v_val_1025_);
return v_v_1026_;
}
else
{
uint8_t v___x_1027_; 
lean_dec(v_val_1025_);
v___x_1027_ = lean_unbox(v_defValue_1021_);
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11___boxed(lean_object* v_opts_1028_, lean_object* v_opt_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_opts_1028_, v_opt_1029_);
lean_dec_ref(v_opt_1029_);
lean_dec_ref(v_opts_1028_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(lean_object* v_ref_1033_, lean_object* v_msgData_1034_, uint8_t v_severity_1035_, uint8_t v_isSilent_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1077_; uint8_t v___y_1078_; uint8_t v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1102_; uint8_t v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; uint8_t v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1113_; uint8_t v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; uint8_t v___y_1119_; uint8_t v___x_1124_; uint8_t v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1131_; uint8_t v___y_1132_; uint8_t v___y_1134_; uint8_t v___x_1149_; 
v___x_1124_ = 2;
v___x_1149_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1035_, v___x_1124_);
if (v___x_1149_ == 0)
{
v___y_1134_ = v___x_1149_;
goto v___jp_1133_;
}
else
{
uint8_t v___x_1150_; 
lean_inc_ref(v_msgData_1034_);
v___x_1150_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1034_);
v___y_1134_ = v___x_1150_;
goto v___jp_1133_;
}
v___jp_1040_:
{
lean_object* v___x_1050_; lean_object* v_currNamespace_1051_; lean_object* v_openDecls_1052_; lean_object* v_env_1053_; lean_object* v_nextMacroScope_1054_; lean_object* v_ngen_1055_; lean_object* v_auxDeclNGen_1056_; lean_object* v_traceState_1057_; lean_object* v_cache_1058_; lean_object* v_messages_1059_; lean_object* v_infoState_1060_; lean_object* v_snapshotTasks_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1075_; 
v___x_1050_ = lean_st_ref_take(v___y_1049_);
v_currNamespace_1051_ = lean_ctor_get(v___y_1048_, 6);
v_openDecls_1052_ = lean_ctor_get(v___y_1048_, 7);
v_env_1053_ = lean_ctor_get(v___x_1050_, 0);
v_nextMacroScope_1054_ = lean_ctor_get(v___x_1050_, 1);
v_ngen_1055_ = lean_ctor_get(v___x_1050_, 2);
v_auxDeclNGen_1056_ = lean_ctor_get(v___x_1050_, 3);
v_traceState_1057_ = lean_ctor_get(v___x_1050_, 4);
v_cache_1058_ = lean_ctor_get(v___x_1050_, 5);
v_messages_1059_ = lean_ctor_get(v___x_1050_, 6);
v_infoState_1060_ = lean_ctor_get(v___x_1050_, 7);
v_snapshotTasks_1061_ = lean_ctor_get(v___x_1050_, 8);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1063_ = v___x_1050_;
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snapshotTasks_1061_);
lean_inc(v_infoState_1060_);
lean_inc(v_messages_1059_);
lean_inc(v_cache_1058_);
lean_inc(v_traceState_1057_);
lean_inc(v_auxDeclNGen_1056_);
lean_inc(v_ngen_1055_);
lean_inc(v_nextMacroScope_1054_);
lean_inc(v_env_1053_);
lean_dec(v___x_1050_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_inc(v_openDecls_1052_);
lean_inc(v_currNamespace_1051_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_currNamespace_1051_);
lean_ctor_set(v___x_1065_, 1, v_openDecls_1052_);
v___x_1066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___y_1042_);
lean_inc_ref(v___y_1044_);
lean_inc_ref(v___y_1047_);
v___x_1067_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1067_, 0, v___y_1047_);
lean_ctor_set(v___x_1067_, 1, v___y_1046_);
lean_ctor_set(v___x_1067_, 2, v___y_1045_);
lean_ctor_set(v___x_1067_, 3, v___y_1044_);
lean_ctor_set(v___x_1067_, 4, v___x_1066_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*5, v___y_1041_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*5 + 1, v___y_1043_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*5 + 2, v_isSilent_1036_);
v___x_1068_ = l_Lean_MessageLog_add(v___x_1067_, v_messages_1059_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 6, v___x_1068_);
v___x_1070_ = v___x_1063_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_env_1053_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_nextMacroScope_1054_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_ngen_1055_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_auxDeclNGen_1056_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_traceState_1057_);
lean_ctor_set(v_reuseFailAlloc_1074_, 5, v_cache_1058_);
lean_ctor_set(v_reuseFailAlloc_1074_, 6, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 7, v_infoState_1060_);
lean_ctor_set(v_reuseFailAlloc_1074_, 8, v_snapshotTasks_1061_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_st_ref_set(v___y_1049_, v___x_1070_);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
v___jp_1076_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1100_; 
v___x_1085_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1034_);
v___x_1086_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v___x_1085_, v___y_1037_, v___y_1038_);
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc_ref_n(v___y_1082_, 2);
v___x_1091_ = l_Lean_FileMap_toPosition(v___y_1082_, v___y_1081_);
lean_dec(v___y_1081_);
v___x_1092_ = l_Lean_FileMap_toPosition(v___y_1082_, v___y_1084_);
lean_dec(v___y_1084_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0));
if (v___y_1079_ == 0)
{
lean_del_object(v___x_1089_);
lean_dec_ref(v___y_1077_);
v___y_1041_ = v___y_1078_;
v___y_1042_ = v_a_1087_;
v___y_1043_ = v___y_1080_;
v___y_1044_ = v___x_1094_;
v___y_1045_ = v___x_1093_;
v___y_1046_ = v___x_1091_;
v___y_1047_ = v___y_1083_;
v___y_1048_ = v___y_1037_;
v___y_1049_ = v___y_1038_;
goto v___jp_1040_;
}
else
{
uint8_t v___x_1095_; 
lean_inc(v_a_1087_);
v___x_1095_ = l_Lean_MessageData_hasTag(v___y_1077_, v_a_1087_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
lean_dec_ref(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec(v_a_1087_);
v___x_1096_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1096_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_del_object(v___x_1089_);
v___y_1041_ = v___y_1078_;
v___y_1042_ = v_a_1087_;
v___y_1043_ = v___y_1080_;
v___y_1044_ = v___x_1094_;
v___y_1045_ = v___x_1093_;
v___y_1046_ = v___x_1091_;
v___y_1047_ = v___y_1083_;
v___y_1048_ = v___y_1037_;
v___y_1049_ = v___y_1038_;
goto v___jp_1040_;
}
}
}
}
v___jp_1101_:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Syntax_getTailPos_x3f(v___y_1107_, v___y_1103_);
lean_dec(v___y_1107_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_inc(v___y_1109_);
v___y_1077_ = v___y_1102_;
v___y_1078_ = v___y_1103_;
v___y_1079_ = v___y_1104_;
v___y_1080_ = v___y_1106_;
v___y_1081_ = v___y_1109_;
v___y_1082_ = v___y_1105_;
v___y_1083_ = v___y_1108_;
v___y_1084_ = v___y_1109_;
goto v___jp_1076_;
}
else
{
lean_object* v_val_1111_; 
v_val_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1111_);
lean_dec_ref(v___x_1110_);
v___y_1077_ = v___y_1102_;
v___y_1078_ = v___y_1103_;
v___y_1079_ = v___y_1104_;
v___y_1080_ = v___y_1106_;
v___y_1081_ = v___y_1109_;
v___y_1082_ = v___y_1105_;
v___y_1083_ = v___y_1108_;
v___y_1084_ = v_val_1111_;
goto v___jp_1076_;
}
}
v___jp_1112_:
{
lean_object* v_ref_1120_; lean_object* v___x_1121_; 
v_ref_1120_ = l_Lean_replaceRef(v_ref_1033_, v___y_1117_);
v___x_1121_ = l_Lean_Syntax_getPos_x3f(v_ref_1120_, v___y_1114_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___y_1102_ = v___y_1113_;
v___y_1103_ = v___y_1114_;
v___y_1104_ = v___y_1115_;
v___y_1105_ = v___y_1116_;
v___y_1106_ = v___y_1119_;
v___y_1107_ = v_ref_1120_;
v___y_1108_ = v___y_1118_;
v___y_1109_ = v___x_1122_;
goto v___jp_1101_;
}
else
{
lean_object* v_val_1123_; 
v_val_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1121_);
v___y_1102_ = v___y_1113_;
v___y_1103_ = v___y_1114_;
v___y_1104_ = v___y_1115_;
v___y_1105_ = v___y_1116_;
v___y_1106_ = v___y_1119_;
v___y_1107_ = v_ref_1120_;
v___y_1108_ = v___y_1118_;
v___y_1109_ = v_val_1123_;
goto v___jp_1101_;
}
}
v___jp_1125_:
{
if (v___y_1132_ == 0)
{
v___y_1113_ = v___y_1128_;
v___y_1114_ = v___y_1131_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v_severity_1035_;
goto v___jp_1112_;
}
else
{
v___y_1113_ = v___y_1128_;
v___y_1114_ = v___y_1131_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___x_1124_;
goto v___jp_1112_;
}
}
v___jp_1133_:
{
if (v___y_1134_ == 0)
{
lean_object* v_fileName_1135_; lean_object* v_fileMap_1136_; lean_object* v_options_1137_; lean_object* v_ref_1138_; uint8_t v_suppressElabErrors_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; uint8_t v___x_1143_; uint8_t v___x_1144_; 
v_fileName_1135_ = lean_ctor_get(v___y_1037_, 0);
v_fileMap_1136_ = lean_ctor_get(v___y_1037_, 1);
v_options_1137_ = lean_ctor_get(v___y_1037_, 2);
v_ref_1138_ = lean_ctor_get(v___y_1037_, 5);
v_suppressElabErrors_1139_ = lean_ctor_get_uint8(v___y_1037_, sizeof(void*)*14 + 1);
v___x_1140_ = lean_box(v___y_1134_);
v___x_1141_ = lean_box(v_suppressElabErrors_1139_);
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1142_, 0, v___x_1140_);
lean_closure_set(v___f_1142_, 1, v___x_1141_);
v___x_1143_ = 1;
v___x_1144_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1035_, v___x_1143_);
if (v___x_1144_ == 0)
{
v___y_1126_ = v_suppressElabErrors_1139_;
v___y_1127_ = v_fileMap_1136_;
v___y_1128_ = v___f_1142_;
v___y_1129_ = v_ref_1138_;
v___y_1130_ = v_fileName_1135_;
v___y_1131_ = v___y_1134_;
v___y_1132_ = v___x_1144_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = l_Lean_warningAsError;
v___x_1146_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_options_1137_, v___x_1145_);
v___y_1126_ = v_suppressElabErrors_1139_;
v___y_1127_ = v_fileMap_1136_;
v___y_1128_ = v___f_1142_;
v___y_1129_ = v_ref_1138_;
v___y_1130_ = v_fileName_1135_;
v___y_1131_ = v___y_1134_;
v___y_1132_ = v___x_1146_;
goto v___jp_1125_;
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_msgData_1034_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_1151_, lean_object* v_msgData_1152_, lean_object* v_severity_1153_, lean_object* v_isSilent_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v_severity_boxed_1158_; uint8_t v_isSilent_boxed_1159_; lean_object* v_res_1160_; 
v_severity_boxed_1158_ = lean_unbox(v_severity_1153_);
v_isSilent_boxed_1159_ = lean_unbox(v_isSilent_1154_);
v_res_1160_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1151_, v_msgData_1152_, v_severity_boxed_1158_, v_isSilent_boxed_1159_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v_ref_1151_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(lean_object* v_msgData_1161_, uint8_t v_severity_1162_, uint8_t v_isSilent_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_ref_1167_; lean_object* v___x_1168_; 
v_ref_1167_ = lean_ctor_get(v___y_1164_, 5);
v___x_1168_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1167_, v_msgData_1161_, v_severity_1162_, v_isSilent_1163_, v___y_1164_, v___y_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1169_, lean_object* v_severity_1170_, lean_object* v_isSilent_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v_severity_boxed_1175_; uint8_t v_isSilent_boxed_1176_; lean_object* v_res_1177_; 
v_severity_boxed_1175_ = lean_unbox(v_severity_1170_);
v_isSilent_boxed_1176_ = lean_unbox(v_isSilent_1171_);
v_res_1177_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1169_, v_severity_boxed_1175_, v_isSilent_boxed_1176_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(lean_object* v_msgData_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = 1;
v___x_1183_ = 0;
v___x_1184_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1178_, v___x_1182_, v___x_1183_, v___y_1179_, v___y_1180_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2___boxed(lean_object* v_msgData_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v_msgData_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0));
v___x_1192_ = l_Lean_stringToMessageData(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object* v_d_1193_, lean_object* v_thmId_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v___y_1223_; uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1193_, v_thmId_1194_);
if (v___x_1237_ == 0)
{
if (lean_obj_tag(v_thmId_1194_) == 0)
{
lean_object* v_declName_1238_; uint8_t v___x_1239_; 
v_declName_1238_ = lean_ctor_get(v_thmId_1194_, 0);
v___x_1239_ = l_Lean_Meta_SimpTheorems_isDeclToUnfold(v_d_1193_, v_declName_1238_);
if (v___x_1239_ == 0)
{
lean_object* v_toUnfoldThms_1240_; uint8_t v___x_1241_; 
v_toUnfoldThms_1240_ = lean_ctor_get(v_d_1193_, 5);
v___x_1241_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_toUnfoldThms_1240_, v_declName_1238_);
v___y_1223_ = v___x_1241_;
goto v___jp_1222_;
}
else
{
v___y_1223_ = v___x_1239_;
goto v___jp_1222_;
}
}
else
{
v___y_1223_ = v___x_1237_;
goto v___jp_1222_;
}
}
else
{
v___y_1223_ = v___x_1237_;
goto v___jp_1222_;
}
v___jp_1198_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1199_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1200_ = l_Lean_Meta_Origin_key(v_thmId_1194_);
lean_dec_ref(v_thmId_1194_);
v___x_1201_ = l_Lean_MessageData_ofName(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1199_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_obj_once(&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1, &l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once, _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v___x_1204_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v___x_1205_, 0);
lean_dec(v_unused_1213_);
v___x_1207_ = v___x_1205_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v___x_1205_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v_d_1193_);
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_d_1193_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_d_1193_);
v_a_1214_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1205_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1205_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
v___jp_1222_:
{
if (v___y_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_inc_ref(v_thmId_1194_);
v___x_1224_ = l_Lean_Meta_Origin_converse(v_thmId_1194_);
if (lean_obj_tag(v___x_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1234_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_val_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
uint8_t v___x_1229_; 
v___x_1229_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1193_, v_val_1225_);
if (v___x_1229_ == 0)
{
lean_del_object(v___x_1227_);
lean_dec(v_val_1225_);
goto v___jp_1198_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
lean_dec_ref(v_thmId_1194_);
v___x_1230_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1193_, v_val_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_dec(v___x_1224_);
goto v___jp_1198_;
}
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1193_, v_thmId_1194_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object* v_d_1242_, lean_object* v_thmId_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v_d_1242_, v_thmId_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object* v_ext_1248_, lean_object* v_attrName_1249_, lean_object* v_declName_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___y_1255_; lean_object* v___x_1317_; 
lean_inc(v_declName_1250_);
v___x_1317_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_1250_, v___y_1252_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; uint8_t v___x_1319_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
v___x_1319_ = lean_unbox(v_a_1318_);
lean_dec(v_a_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec_ref(v___x_1317_);
v___x_1320_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_1250_, v___y_1252_);
v___y_1255_ = v___x_1320_;
goto v___jp_1254_;
}
else
{
v___y_1255_ = v___x_1317_;
goto v___jp_1254_;
}
}
else
{
v___y_1255_ = v___x_1317_;
goto v___jp_1254_;
}
v___jp_1254_:
{
if (lean_obj_tag(v___y_1255_) == 0)
{
lean_object* v_a_1256_; uint8_t v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___y_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___y_1255_);
v___x_1257_ = lean_unbox(v_a_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v_ext_1259_; lean_object* v_toEnvExtension_1260_; lean_object* v_env_1261_; lean_object* v_asyncMode_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; 
lean_dec(v_attrName_1249_);
v___x_1258_ = lean_st_ref_get(v___y_1252_);
v_ext_1259_ = lean_ctor_get(v_ext_1248_, 1);
v_toEnvExtension_1260_ = lean_ctor_get(v_ext_1259_, 0);
v_env_1261_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_ref(v_env_1261_);
lean_dec(v___x_1258_);
v_asyncMode_1262_ = lean_ctor_get(v_toEnvExtension_1260_, 2);
v___x_1263_ = 1;
v___x_1264_ = l_Lean_Meta_instInhabitedSimpTheorems_default;
v___x_1265_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1264_, v_ext_1248_, v_env_1261_, v_asyncMode_1262_);
v___x_1266_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1266_, 0, v_declName_1250_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*1, v___x_1263_);
v___x_1267_ = lean_unbox(v_a_1256_);
lean_dec(v_a_1256_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*1 + 1, v___x_1267_);
v___x_1268_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v___x_1265_, v___x_1266_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1298_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1298_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1298_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v_env_1274_; lean_object* v_nextMacroScope_1275_; lean_object* v_ngen_1276_; lean_object* v_auxDeclNGen_1277_; lean_object* v_traceState_1278_; lean_object* v_messages_1279_; lean_object* v_infoState_1280_; lean_object* v_snapshotTasks_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1296_; 
v___x_1273_ = lean_st_ref_take(v___y_1252_);
v_env_1274_ = lean_ctor_get(v___x_1273_, 0);
v_nextMacroScope_1275_ = lean_ctor_get(v___x_1273_, 1);
v_ngen_1276_ = lean_ctor_get(v___x_1273_, 2);
v_auxDeclNGen_1277_ = lean_ctor_get(v___x_1273_, 3);
v_traceState_1278_ = lean_ctor_get(v___x_1273_, 4);
v_messages_1279_ = lean_ctor_get(v___x_1273_, 6);
v_infoState_1280_ = lean_ctor_get(v___x_1273_, 7);
v_snapshotTasks_1281_ = lean_ctor_get(v___x_1273_, 8);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v___x_1273_, 5);
lean_dec(v_unused_1297_);
v___x_1283_ = v___x_1273_;
v_isShared_1284_ = v_isSharedCheck_1296_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snapshotTasks_1281_);
lean_inc(v_infoState_1280_);
lean_inc(v_messages_1279_);
lean_inc(v_traceState_1278_);
lean_inc(v_auxDeclNGen_1277_);
lean_inc(v_ngen_1276_);
lean_inc(v_nextMacroScope_1275_);
lean_inc(v_env_1274_);
lean_dec(v___x_1273_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1296_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1285_, 0, v_a_1269_);
v___x_1286_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1248_, v_env_1274_, v___f_1285_);
v___x_1287_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 5, v___x_1287_);
lean_ctor_set(v___x_1283_, 0, v___x_1286_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_nextMacroScope_1275_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_ngen_1276_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_auxDeclNGen_1277_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_traceState_1278_);
lean_ctor_set(v_reuseFailAlloc_1295_, 5, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1295_, 6, v_messages_1279_);
lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_infoState_1280_);
lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_snapshotTasks_1281_);
v___x_1289_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_st_ref_set(v___y_1252_, v___x_1289_);
v___x_1291_ = lean_box(0);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1291_);
v___x_1293_ = v___x_1271_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_ext_1248_);
v_a_1299_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1268_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1268_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v_a_1256_);
lean_dec_ref(v_ext_1248_);
v___x_1307_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_1249_);
v___x_1308_ = l_Lean_Attribute_erase(v_declName_1250_, v___x_1307_, v___y_1251_, v___y_1252_);
return v___x_1308_;
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_declName_1250_);
lean_dec(v_attrName_1249_);
lean_dec_ref(v_ext_1248_);
v_a_1309_ = lean_ctor_get(v___y_1255_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___y_1255_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___y_1255_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___y_1255_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object* v_ext_1321_, lean_object* v_attrName_1322_, lean_object* v_declName_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Meta_mkSimpAttr___lam__2(v_ext_1321_, v_attrName_1322_, v_declName_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* v_attrName_1328_, lean_object* v_attrDescr_1329_, lean_object* v_ext_1330_, lean_object* v_ref_1331_){
_start:
{
lean_object* v___f_1333_; lean_object* v___f_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_inc_n(v_attrName_1328_, 2);
lean_inc_ref(v_ext_1330_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1333_, 0, v_ext_1330_);
lean_closure_set(v___f_1333_, 1, v_attrName_1328_);
v___f_1334_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 6, 2);
lean_closure_set(v___f_1334_, 0, v_ext_1330_);
lean_closure_set(v___f_1334_, 1, v_attrName_1328_);
v___x_1335_ = 1;
v___x_1336_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1336_, 0, v_ref_1331_);
lean_ctor_set(v___x_1336_, 1, v_attrName_1328_);
lean_ctor_set(v___x_1336_, 2, v_attrDescr_1329_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*3, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___f_1333_);
lean_ctor_set(v___x_1337_, 2, v___f_1334_);
v___x_1338_ = l_Lean_registerBuiltinAttribute(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___boxed(lean_object* v_attrName_1339_, lean_object* v_attrDescr_1340_, lean_object* v_ext_1341_, lean_object* v_ref_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_mkSimpAttr(v_attrName_1339_, v_attrDescr_1340_, v_ext_1341_, v_ref_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(lean_object* v_00_u03b1_1345_, lean_object* v_constName_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_constName_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(v_00_u03b1_1353_, v_constName_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1360_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(lean_object* v_00_u03b2_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
uint8_t v___x_1364_; 
v___x_1364_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_1362_, v_x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(v_00_u03b2_1365_, v_x_1366_, v_x_1367_);
lean_dec(v_x_1367_);
lean_dec_ref(v_x_1366_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1370_, lean_object* v_ref_1371_, lean_object* v_constName_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1371_, v_constName_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_ref_1380_, lean_object* v_constName_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_1379_, v_ref_1380_, v_constName_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v_ref_1380_);
return v_res_1387_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, size_t v_x_1390_, lean_object* v_x_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_1389_, v_x_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
size_t v_x_10026__boxed_1397_; uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_x_10026__boxed_1397_ = lean_unbox_usize(v_x_1395_);
lean_dec(v_x_1395_);
v_res_1398_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(v_00_u03b2_1393_, v_x_1394_, v_x_10026__boxed_1397_, v_x_1396_);
lean_dec(v_x_1396_);
lean_dec_ref(v_x_1394_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1400_, lean_object* v_ref_1401_, lean_object* v_msg_1402_, lean_object* v_declHint_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1401_, v_msg_1402_, v_declHint_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_ref_1411_, lean_object* v_msg_1412_, lean_object* v_declHint_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1410_, v_ref_1411_, v_msg_1412_, v_declHint_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v_ref_1411_);
return v_res_1419_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1420_, lean_object* v_keys_1421_, lean_object* v_vals_1422_, lean_object* v_heq_1423_, lean_object* v_i_1424_, lean_object* v_k_1425_){
_start:
{
uint8_t v___x_1426_; 
v___x_1426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_1421_, v_i_1424_, v_k_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1427_, lean_object* v_keys_1428_, lean_object* v_vals_1429_, lean_object* v_heq_1430_, lean_object* v_i_1431_, lean_object* v_k_1432_){
_start:
{
uint8_t v_res_1433_; lean_object* v_r_1434_; 
v_res_1433_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_1427_, v_keys_1428_, v_vals_1429_, v_heq_1430_, v_i_1431_, v_k_1432_);
lean_dec(v_k_1432_);
lean_dec_ref(v_vals_1429_);
lean_dec_ref(v_keys_1428_);
v_r_1434_ = lean_box(v_res_1433_);
return v_r_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(lean_object* v_msg_1435_, lean_object* v_declHint_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_1435_, v_declHint_1436_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_msg_1443_, lean_object* v_declHint_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(v_msg_1443_, v_declHint_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b1_1451_, lean_object* v_ref_1452_, lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1452_, v_msg_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_1460_, v_ref_1461_, v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v_ref_1461_);
return v_res_1468_;
}
}
static lean_object* _init_l_Lean_Meta_registerSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_1470_, lean_object* v_b_1471_, lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_dec(v_b_1471_);
lean_dec(v_a_1470_);
return v_x_1472_;
}
else
{
lean_object* v_key_1473_; lean_object* v_value_1474_; lean_object* v_tail_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1487_; 
v_key_1473_ = lean_ctor_get(v_x_1472_, 0);
v_value_1474_ = lean_ctor_get(v_x_1472_, 1);
v_tail_1475_ = lean_ctor_get(v_x_1472_, 2);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_x_1472_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1477_ = v_x_1472_;
v_isShared_1478_ = v_isSharedCheck_1487_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_tail_1475_);
lean_inc(v_value_1474_);
lean_inc(v_key_1473_);
lean_dec(v_x_1472_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1487_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_name_eq(v_key_1473_, v_a_1470_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1470_, v_b_1471_, v_tail_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 2, v___x_1480_);
v___x_1482_ = v___x_1477_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_key_1473_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_value_1474_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
else
{
lean_object* v___x_1485_; 
lean_dec(v_value_1474_);
lean_dec(v_key_1473_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v_b_1471_);
lean_ctor_set(v___x_1477_, 0, v_a_1470_);
v___x_1485_ = v___x_1477_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1470_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_b_1471_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_tail_1475_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
if (lean_obj_tag(v_x_1489_) == 0)
{
return v_x_1488_;
}
else
{
lean_object* v_key_1490_; lean_object* v_value_1491_; lean_object* v_tail_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1518_; 
v_key_1490_ = lean_ctor_get(v_x_1489_, 0);
v_value_1491_ = lean_ctor_get(v_x_1489_, 1);
v_tail_1492_ = lean_ctor_get(v_x_1489_, 2);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_x_1489_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1494_ = v_x_1489_;
v_isShared_1495_ = v_isSharedCheck_1518_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_tail_1492_);
lean_inc(v_value_1491_);
lean_inc(v_key_1490_);
lean_dec(v_x_1489_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1518_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; uint64_t v___y_1498_; 
v___x_1496_ = lean_array_get_size(v_x_1488_);
if (lean_obj_tag(v_key_1490_) == 0)
{
uint64_t v___x_1516_; 
v___x_1516_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0);
v___y_1498_ = v___x_1516_;
goto v___jp_1497_;
}
else
{
uint64_t v_hash_1517_; 
v_hash_1517_ = lean_ctor_get_uint64(v_key_1490_, sizeof(void*)*2);
v___y_1498_ = v_hash_1517_;
goto v___jp_1497_;
}
v___jp_1497_:
{
uint64_t v___x_1499_; uint64_t v___x_1500_; uint64_t v_fold_1501_; uint64_t v___x_1502_; uint64_t v___x_1503_; uint64_t v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1499_ = 32ULL;
v___x_1500_ = lean_uint64_shift_right(v___y_1498_, v___x_1499_);
v_fold_1501_ = lean_uint64_xor(v___y_1498_, v___x_1500_);
v___x_1502_ = 16ULL;
v___x_1503_ = lean_uint64_shift_right(v_fold_1501_, v___x_1502_);
v___x_1504_ = lean_uint64_xor(v_fold_1501_, v___x_1503_);
v___x_1505_ = lean_uint64_to_usize(v___x_1504_);
v___x_1506_ = lean_usize_of_nat(v___x_1496_);
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_sub(v___x_1506_, v___x_1507_);
v___x_1509_ = lean_usize_land(v___x_1505_, v___x_1508_);
v___x_1510_ = lean_array_uget_borrowed(v_x_1488_, v___x_1509_);
lean_inc(v___x_1510_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 2, v___x_1510_);
v___x_1512_ = v___x_1494_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_key_1490_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_value_1491_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_array_uset(v_x_1488_, v___x_1509_, v___x_1512_);
v_x_1488_ = v___x_1513_;
v_x_1489_ = v_tail_1492_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1519_, lean_object* v_source_1520_, lean_object* v_target_1521_){
_start:
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_array_get_size(v_source_1520_);
v___x_1523_ = lean_nat_dec_lt(v_i_1519_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec_ref(v_source_1520_);
lean_dec(v_i_1519_);
return v_target_1521_;
}
else
{
lean_object* v_es_1524_; lean_object* v___x_1525_; lean_object* v_source_1526_; lean_object* v_target_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_es_1524_ = lean_array_fget(v_source_1520_, v_i_1519_);
v___x_1525_ = lean_box(0);
v_source_1526_ = lean_array_fset(v_source_1520_, v_i_1519_, v___x_1525_);
v_target_1527_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1521_, v_es_1524_);
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_nat_add(v_i_1519_, v___x_1528_);
lean_dec(v_i_1519_);
v_i_1519_ = v___x_1529_;
v_source_1520_ = v_source_1526_;
v_target_1521_ = v_target_1527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_nbuckets_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1532_ = lean_array_get_size(v_data_1531_);
v___x_1533_ = lean_unsigned_to_nat(2u);
v_nbuckets_1534_ = lean_nat_mul(v___x_1532_, v___x_1533_);
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_mk_array(v_nbuckets_1534_, v___x_1536_);
v___x_1538_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_1535_, v_data_1531_, v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
uint8_t v___x_1541_; 
v___x_1541_ = 0;
return v___x_1541_;
}
else
{
lean_object* v_key_1542_; lean_object* v_tail_1543_; uint8_t v___x_1544_; 
v_key_1542_ = lean_ctor_get(v_x_1540_, 0);
v_tail_1543_ = lean_ctor_get(v_x_1540_, 2);
v___x_1544_ = lean_name_eq(v_key_1542_, v_a_1539_);
if (v___x_1544_ == 0)
{
v_x_1540_ = v_tail_1543_;
goto _start;
}
else
{
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_1546_, lean_object* v_x_1547_){
_start:
{
uint8_t v_res_1548_; lean_object* v_r_1549_; 
v_res_1548_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1546_, v_x_1547_);
lean_dec(v_x_1547_);
lean_dec(v_a_1546_);
v_r_1549_ = lean_box(v_res_1548_);
return v_r_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(lean_object* v_m_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_){
_start:
{
lean_object* v_size_1553_; lean_object* v_buckets_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1600_; 
v_size_1553_ = lean_ctor_get(v_m_1550_, 0);
v_buckets_1554_ = lean_ctor_get(v_m_1550_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_m_1550_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1556_ = v_m_1550_;
v_isShared_1557_ = v_isSharedCheck_1600_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_buckets_1554_);
lean_inc(v_size_1553_);
lean_dec(v_m_1550_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1600_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; uint64_t v___y_1560_; 
v___x_1558_ = lean_array_get_size(v_buckets_1554_);
if (lean_obj_tag(v_a_1551_) == 0)
{
uint64_t v___x_1598_; 
v___x_1598_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0);
v___y_1560_ = v___x_1598_;
goto v___jp_1559_;
}
else
{
uint64_t v_hash_1599_; 
v_hash_1599_ = lean_ctor_get_uint64(v_a_1551_, sizeof(void*)*2);
v___y_1560_ = v_hash_1599_;
goto v___jp_1559_;
}
v___jp_1559_:
{
uint64_t v___x_1561_; uint64_t v___x_1562_; uint64_t v_fold_1563_; uint64_t v___x_1564_; uint64_t v___x_1565_; uint64_t v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; lean_object* v_bkt_1572_; uint8_t v___x_1573_; 
v___x_1561_ = 32ULL;
v___x_1562_ = lean_uint64_shift_right(v___y_1560_, v___x_1561_);
v_fold_1563_ = lean_uint64_xor(v___y_1560_, v___x_1562_);
v___x_1564_ = 16ULL;
v___x_1565_ = lean_uint64_shift_right(v_fold_1563_, v___x_1564_);
v___x_1566_ = lean_uint64_xor(v_fold_1563_, v___x_1565_);
v___x_1567_ = lean_uint64_to_usize(v___x_1566_);
v___x_1568_ = lean_usize_of_nat(v___x_1558_);
v___x_1569_ = ((size_t)1ULL);
v___x_1570_ = lean_usize_sub(v___x_1568_, v___x_1569_);
v___x_1571_ = lean_usize_land(v___x_1567_, v___x_1570_);
v_bkt_1572_ = lean_array_uget_borrowed(v_buckets_1554_, v___x_1571_);
v___x_1573_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1551_, v_bkt_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v_size_x27_1575_; lean_object* v___x_1576_; lean_object* v_buckets_x27_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v_size_x27_1575_ = lean_nat_add(v_size_1553_, v___x_1574_);
lean_dec(v_size_1553_);
lean_inc(v_bkt_1572_);
v___x_1576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1576_, 0, v_a_1551_);
lean_ctor_set(v___x_1576_, 1, v_b_1552_);
lean_ctor_set(v___x_1576_, 2, v_bkt_1572_);
v_buckets_x27_1577_ = lean_array_uset(v_buckets_1554_, v___x_1571_, v___x_1576_);
v___x_1578_ = lean_unsigned_to_nat(4u);
v___x_1579_ = lean_nat_mul(v_size_x27_1575_, v___x_1578_);
v___x_1580_ = lean_unsigned_to_nat(3u);
v___x_1581_ = lean_nat_div(v___x_1579_, v___x_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_array_get_size(v_buckets_x27_1577_);
v___x_1583_ = lean_nat_dec_le(v___x_1581_, v___x_1582_);
lean_dec(v___x_1581_);
if (v___x_1583_ == 0)
{
lean_object* v_val_1584_; lean_object* v___x_1586_; 
v_val_1584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_1577_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v_val_1584_);
lean_ctor_set(v___x_1556_, 0, v_size_x27_1575_);
v___x_1586_ = v___x_1556_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_size_x27_1575_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_val_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
lean_object* v___x_1589_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v_buckets_x27_1577_);
lean_ctor_set(v___x_1556_, 0, v_size_x27_1575_);
v___x_1589_ = v___x_1556_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_size_x27_1575_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_buckets_x27_1577_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
else
{
lean_object* v___x_1591_; lean_object* v_buckets_x27_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_inc(v_bkt_1572_);
v___x_1591_ = lean_box(0);
v_buckets_x27_1592_ = lean_array_uset(v_buckets_1554_, v___x_1571_, v___x_1591_);
v___x_1593_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1551_, v_b_1552_, v_bkt_1572_);
v___x_1594_ = lean_array_uset(v_buckets_x27_1592_, v___x_1571_, v___x_1593_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v___x_1594_);
v___x_1596_ = v___x_1556_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_size_1553_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* v_attrName_1601_, lean_object* v_attrDescr_1602_, lean_object* v_ref_1603_){
_start:
{
lean_object* v___x_1605_; 
lean_inc(v_ref_1603_);
v___x_1605_ = l_Lean_Meta_mkSimpExt(v_ref_1603_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_n(v_a_1606_, 2);
lean_dec_ref(v___x_1605_);
lean_inc(v_attrName_1601_);
v___x_1607_ = l_Lean_Meta_mkSimpAttr(v_attrName_1601_, v_attrDescr_1602_, v_a_1606_, v_ref_1603_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1618_; 
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v___x_1607_, 0);
lean_dec(v_unused_1619_);
v___x_1609_ = v___x_1607_;
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
else
{
lean_dec(v___x_1607_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1611_ = l_Lean_Meta_simpExtensionMapRef;
v___x_1612_ = lean_st_ref_take(v___x_1611_);
lean_inc(v_a_1606_);
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v___x_1612_, v_attrName_1601_, v_a_1606_);
v___x_1614_ = lean_st_ref_set(v___x_1611_, v___x_1613_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_a_1606_);
v___x_1616_ = v___x_1609_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1606_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_a_1606_);
lean_dec(v_attrName_1601_);
v_a_1620_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1607_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1607_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_dec(v_ref_1603_);
lean_dec_ref(v_attrDescr_1602_);
lean_dec(v_attrName_1601_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___boxed(lean_object* v_attrName_1628_, lean_object* v_attrDescr_1629_, lean_object* v_ref_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_registerSimpAttr(v_attrName_1628_, v_attrDescr_1629_, v_ref_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(lean_object* v_00_u03b2_1633_, lean_object* v_m_1634_, lean_object* v_a_1635_, lean_object* v_b_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v_m_1634_, v_a_1635_, v_b_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_1638_, lean_object* v_a_1639_, lean_object* v_x_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_a_1643_, lean_object* v_x_1644_){
_start:
{
uint8_t v_res_1645_; lean_object* v_r_1646_; 
v_res_1645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(v_00_u03b2_1642_, v_a_1643_, v_x_1644_);
lean_dec(v_x_1644_);
lean_dec(v_a_1643_);
v_r_1646_ = lean_box(v_res_1645_);
return v_r_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_1647_, lean_object* v_data_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_data_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_1650_, lean_object* v_a_1651_, lean_object* v_b_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1651_, v_b_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1655_, lean_object* v_i_1656_, lean_object* v_source_1657_, lean_object* v_target_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_1656_, v_source_1657_, v_target_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1661_, v_x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1678_ = l_Lean_Meta_registerSimpAttr(v___x_1675_, v___x_1676_, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1694_ = l_Lean_Meta_registerSimpAttr(v___x_1691_, v___x_1692_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = l_Lean_Meta_simpExtension;
v___x_1700_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1699_, v_a_1697_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1701_);
lean_dec(v_a_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Meta_getSimpTheorems(v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = l_Lean_Meta_sevalSimpExtension;
v___x_1715_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1714_, v_a_1712_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1716_);
lean_dec(v_a_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_getSEvalTheorems(v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1736_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = ((lean_object*)(l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0));
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_mk_empty_array_with_capacity(v___x_1743_);
v___x_1745_ = lean_array_push(v___x_1744_, v_a_1739_);
v___x_1746_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1742_, v___x_1745_, v_a_1741_, v_a_1734_, v_a_1735_, v_a_1736_);
return v___x_1746_;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1739_);
v_a_1747_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1740_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1740_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
v_a_1755_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1738_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1738_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1768_, v_a_1770_, v_a_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Meta_Simp_Context_mkDefault(v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1779_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_sevalSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_sevalSimpExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Meta_mkSimpAttr___auto__1 = _init_l_Lean_Meta_mkSimpAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___auto__1);
l_Lean_Meta_registerSimpAttr___auto__1 = _init_l_Lean_Meta_registerSimpAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_registerSimpAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
