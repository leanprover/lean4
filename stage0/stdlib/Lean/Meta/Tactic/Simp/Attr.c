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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_currNamespace_29_ = lean_ctor_get(v___y_26_, 5);
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
v___x_46_ = lean_st_ref_put(v___y_27_, v___x_45_);
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
v___x_58_ = lean_st_ref_put(v___y_25_, v___x_57_);
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
v_options_112_ = lean_ctor_get(v___y_104_, 1);
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
v_ref_129_ = lean_ctor_get(v___y_126_, 4);
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
lean_dec_ref_known(v___x_164_, 1);
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
uint8_t v_post_boxed_183_; uint8_t v_a_3790__boxed_184_; uint8_t v_attrKind_boxed_185_; size_t v_sz_boxed_186_; size_t v_i_boxed_187_; lean_object* v_res_188_; 
v_post_boxed_183_ = lean_unbox(v_post_170_);
v_a_3790__boxed_184_ = lean_unbox(v_a_171_);
v_attrKind_boxed_185_ = lean_unbox(v_attrKind_172_);
v_sz_boxed_186_ = lean_unbox_usize(v_sz_175_);
lean_dec(v_sz_175_);
v_i_boxed_187_ = lean_unbox_usize(v_i_176_);
lean_dec(v_i_176_);
v_res_188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_169_, v_post_boxed_183_, v_a_3790__boxed_184_, v_attrKind_boxed_185_, v_prio_173_, v_as_174_, v_sz_boxed_186_, v_i_boxed_187_, v_b_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
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
lean_dec_ref_known(v___x_230_, 1);
if (lean_obj_tag(v_a_231_) == 1)
{
lean_object* v_val_232_; lean_object* v___x_233_; size_t v_sz_234_; size_t v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_227_);
v_val_232_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v_a_231_, 1);
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
lean_dec_ref_known(v___x_237_, 1);
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
v___x_444_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_444_, 10, v___x_442_);
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
lean_object* v_toCold_580_; lean_object* v_options_581_; lean_object* v_currRecDepth_582_; lean_object* v_maxRecDepth_583_; lean_object* v_ref_584_; lean_object* v_currNamespace_585_; lean_object* v_openDecls_586_; lean_object* v_initHeartbeats_587_; lean_object* v_maxHeartbeats_588_; lean_object* v_currMacroScope_589_; uint8_t v_diag_590_; uint8_t v_suppressElabErrors_591_; lean_object* v_ref_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_toCold_580_ = lean_ctor_get(v___y_577_, 0);
v_options_581_ = lean_ctor_get(v___y_577_, 1);
v_currRecDepth_582_ = lean_ctor_get(v___y_577_, 2);
v_maxRecDepth_583_ = lean_ctor_get(v___y_577_, 3);
v_ref_584_ = lean_ctor_get(v___y_577_, 4);
v_currNamespace_585_ = lean_ctor_get(v___y_577_, 5);
v_openDecls_586_ = lean_ctor_get(v___y_577_, 6);
v_initHeartbeats_587_ = lean_ctor_get(v___y_577_, 7);
v_maxHeartbeats_588_ = lean_ctor_get(v___y_577_, 8);
v_currMacroScope_589_ = lean_ctor_get(v___y_577_, 9);
v_diag_590_ = lean_ctor_get_uint8(v___y_577_, sizeof(void*)*10);
v_suppressElabErrors_591_ = lean_ctor_get_uint8(v___y_577_, sizeof(void*)*10 + 1);
v_ref_592_ = l_Lean_replaceRef(v_ref_573_, v_ref_584_);
lean_inc(v_currMacroScope_589_);
lean_inc(v_maxHeartbeats_588_);
lean_inc(v_initHeartbeats_587_);
lean_inc(v_openDecls_586_);
lean_inc(v_currNamespace_585_);
lean_inc(v_maxRecDepth_583_);
lean_inc(v_currRecDepth_582_);
lean_inc_ref(v_options_581_);
lean_inc_ref(v_toCold_580_);
v___x_593_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_593_, 0, v_toCold_580_);
lean_ctor_set(v___x_593_, 1, v_options_581_);
lean_ctor_set(v___x_593_, 2, v_currRecDepth_582_);
lean_ctor_set(v___x_593_, 3, v_maxRecDepth_583_);
lean_ctor_set(v___x_593_, 4, v_ref_592_);
lean_ctor_set(v___x_593_, 5, v_currNamespace_585_);
lean_ctor_set(v___x_593_, 6, v_openDecls_586_);
lean_ctor_set(v___x_593_, 7, v_initHeartbeats_587_);
lean_ctor_set(v___x_593_, 8, v_maxHeartbeats_588_);
lean_ctor_set(v___x_593_, 9, v_currMacroScope_589_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*10, v_diag_590_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*10 + 1, v_suppressElabErrors_591_);
v___x_594_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_574_, v___y_575_, v___y_576_, v___x_593_, v___y_578_);
lean_dec_ref_known(v___x_593_, 10);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_ref_595_, lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_595_, v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v_ref_595_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_603_, lean_object* v_msg_604_, lean_object* v_declHint_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; lean_object* v_a_612_; lean_object* v___x_613_; 
v___x_611_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_604_, v_declHint_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref(v___x_611_);
v___x_613_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_603_, v_a_612_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_614_, lean_object* v_msg_615_, lean_object* v_declHint_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_614_, v_msg_615_, v_declHint_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v_ref_614_);
return v_res_622_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_629_, lean_object* v_constName_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_636_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_637_ = 0;
lean_inc(v_constName_630_);
v___x_638_ = l_Lean_MessageData_ofConstName(v_constName_630_, v___x_637_);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_636_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_629_, v___x_641_, v_constName_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_643_, lean_object* v_constName_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_643_, v_constName_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v_ref_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object* v_constName_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_ref_657_; lean_object* v___x_658_; 
v_ref_657_ = lean_ctor_get(v___y_654_, 4);
v___x_658_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_657_, v_constName_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_constName_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object* v_constName_666_, uint8_t v_skipRealize_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v_env_674_; lean_object* v___x_675_; 
v___x_673_ = lean_st_ref_get(v___y_671_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_env_674_);
lean_dec(v___x_673_);
lean_inc(v_constName_666_);
v___x_675_ = l_Lean_Environment_findAsync_x3f(v_env_674_, v_constName_666_, v_skipRealize_667_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_666_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v___x_676_;
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_constName_666_);
v_val_677_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_675_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v___x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 0);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_val_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object* v_constName_685_, lean_object* v_skipRealize_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_skipRealize_boxed_692_; lean_object* v_res_693_; 
v_skipRealize_boxed_692_ = lean_unbox(v_skipRealize_686_);
v_res_693_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_constName_685_, v_skipRealize_boxed_692_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_693_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__0));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__2));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__4));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__5, &l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5);
v___x_704_ = l_Lean_MessageData_note(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_705_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__7, &l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_box(1);
v___x_709_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_710_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_708_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_ctor_set(v___x_716_, 3, v___x_715_);
lean_ctor_set(v___x_716_, 4, v___x_714_);
lean_ctor_set(v___x_716_, 5, v___x_714_);
lean_ctor_set(v___x_716_, 6, v___x_714_);
lean_ctor_set(v___x_716_, 7, v___x_714_);
lean_ctor_set(v___x_716_, 8, v___x_714_);
lean_ctor_set(v___x_716_, 9, v___x_714_);
lean_ctor_set(v___x_716_, 10, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
lean_ctor_set(v___x_718_, 3, v___x_717_);
lean_ctor_set(v___x_718_, 4, v___x_717_);
lean_ctor_set(v___x_718_, 5, v___x_717_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_ctor_set(v___x_720_, 2, v___x_719_);
lean_ctor_set(v___x_720_, 3, v___x_719_);
lean_ctor_set(v___x_720_, 4, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object* v_ext_727_, lean_object* v___x_728_, lean_object* v_attrName_729_, lean_object* v_declName_730_, lean_object* v_stx_731_, uint8_t v_attrKind_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_746_; uint8_t v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; uint8_t v___y_751_; uint8_t v___y_752_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; uint8_t v___y_805_; uint8_t v___y_806_; lean_object* v___y_811_; lean_object* v___x_873_; 
lean_inc(v_declName_730_);
v___x_873_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_730_, v___y_734_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
v___x_875_ = lean_unbox(v_a_874_);
lean_dec(v_a_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref_known(v___x_873_, 1);
v___x_876_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_730_, v___y_734_);
v___y_811_ = v___x_876_;
goto v___jp_810_;
}
else
{
v___y_811_ = v___x_873_;
goto v___jp_810_;
}
}
else
{
v___y_811_ = v___x_873_;
goto v___jp_810_;
}
v___jp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_st_ref_get(v___y_738_);
lean_dec(v___y_738_);
lean_dec(v___x_739_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___y_737_);
return v___x_740_;
}
v___jp_741_:
{
if (lean_obj_tag(v___y_744_) == 0)
{
lean_dec_ref_known(v___y_744_, 1);
v___y_737_ = v___y_742_;
v___y_738_ = v___y_743_;
goto v___jp_736_;
}
else
{
lean_dec(v___y_743_);
return v___y_744_;
}
}
v___jp_745_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(3u);
v___x_754_ = l_Lean_Syntax_getArg(v_stx_731_, v___x_753_);
lean_dec(v_stx_731_);
v___x_755_ = l_Lean_getAttrParamOptPrio(v___x_754_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v_sig_757_; lean_object* v___x_758_; lean_object* v_type_759_; lean_object* v___x_760_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v_sig_757_ = lean_ctor_get(v___y_749_, 1);
lean_inc_ref(v_sig_757_);
lean_dec_ref(v___y_749_);
v___x_758_ = lean_task_get_own(v_sig_757_);
v_type_759_ = lean_ctor_get(v___x_758_, 2);
lean_inc_ref(v_type_759_);
lean_dec(v___x_758_);
v___x_760_ = l_Lean_Meta_isProp(v_type_759_, v___y_748_, v___y_750_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; uint8_t v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = lean_unbox(v_a_761_);
lean_dec(v_a_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_inc(v_declName_730_);
v___x_763_ = l_Lean_Meta_addDeclToUnfold(v_ext_727_, v_declName_730_, v___y_747_, v___y_752_, v_a_756_, v_attrKind_732_, v___y_748_, v___y_750_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; uint8_t v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = lean_unbox(v_a_764_);
lean_dec(v_a_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_766_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__1, &l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1);
v___x_767_ = l_Lean_MessageData_ofConstName(v_declName_730_, v___y_751_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__6, &l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_772_, v___y_748_, v___y_750_, v___y_733_, v___y_734_);
lean_dec_ref(v___y_748_);
v___y_742_ = v___y_746_;
v___y_743_ = v___y_750_;
v___y_744_ = v___x_773_;
goto v___jp_741_;
}
else
{
lean_dec_ref(v___y_748_);
lean_dec(v_declName_730_);
v___y_737_ = v___y_746_;
v___y_738_ = v___y_750_;
goto v___jp_736_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v___y_750_);
lean_dec_ref(v___y_748_);
lean_dec(v_declName_730_);
v_a_774_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_763_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_763_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_addSimpTheorem(v_ext_727_, v_declName_730_, v___y_747_, v___y_752_, v_attrKind_732_, v_a_756_, v___y_748_, v___y_750_, v___y_733_, v___y_734_);
lean_dec_ref(v___y_748_);
v___y_742_ = v___y_746_;
v___y_743_ = v___y_750_;
v___y_744_ = v___x_782_;
goto v___jp_741_;
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_756_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_748_);
lean_dec(v_declName_730_);
lean_dec_ref(v_ext_727_);
v_a_783_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_760_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_760_);
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
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v_declName_730_);
lean_dec_ref(v_ext_727_);
v_a_791_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_755_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_755_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
v___jp_799_:
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_807_ = lean_unsigned_to_nat(2u);
v___x_808_ = l_Lean_Syntax_getArg(v_stx_731_, v___x_807_);
v___x_809_ = l_Lean_Syntax_isNone(v___x_808_);
lean_dec(v___x_808_);
if (v___x_809_ == 0)
{
v___y_746_ = v___y_801_;
v___y_747_ = v___y_806_;
v___y_748_ = v___y_800_;
v___y_749_ = v___y_802_;
v___y_750_ = v___y_803_;
v___y_751_ = v___y_804_;
v___y_752_ = v___y_805_;
goto v___jp_745_;
}
else
{
v___y_746_ = v___y_801_;
v___y_747_ = v___y_806_;
v___y_748_ = v___y_800_;
v___y_749_ = v___y_802_;
v___y_750_ = v___y_803_;
v___y_751_ = v___y_804_;
v___y_752_ = v___y_804_;
goto v___jp_745_;
}
}
v___jp_810_:
{
if (lean_obj_tag(v___y_811_) == 0)
{
lean_object* v_a_812_; uint8_t v___x_813_; 
v_a_812_ = lean_ctor_get(v___y_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___y_811_, 1);
v___x_813_ = lean_unbox(v_a_812_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; uint8_t v___x_815_; uint8_t v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; uint8_t v___x_820_; uint8_t v___x_821_; uint8_t v___x_822_; uint8_t v___x_823_; uint8_t v___x_824_; uint8_t v___x_825_; uint64_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; uint8_t v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
lean_dec(v_attrName_729_);
v___x_814_ = 1;
v___x_815_ = 1;
v___x_816_ = 0;
v___x_817_ = 2;
v___x_818_ = lean_alloc_ctor(0, 0, 20);
v___x_819_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 0, v___x_819_);
v___x_820_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 1, v___x_820_);
v___x_821_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 2, v___x_821_);
v___x_822_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 3, v___x_822_);
v___x_823_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 4, v___x_823_);
lean_ctor_set_uint8(v___x_818_, 5, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 6, v___x_814_);
v___x_824_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 7, v___x_824_);
lean_ctor_set_uint8(v___x_818_, 8, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 9, v___x_815_);
lean_ctor_set_uint8(v___x_818_, 10, v___x_816_);
lean_ctor_set_uint8(v___x_818_, 11, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 12, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 13, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 14, v___x_817_);
lean_ctor_set_uint8(v___x_818_, 15, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 16, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 17, v___x_814_);
lean_ctor_set_uint8(v___x_818_, 18, v___x_814_);
v___x_825_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_818_, 19, v___x_825_);
v___x_826_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_818_);
v___x_827_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_827_, 0, v___x_818_);
lean_ctor_set_uint64(v___x_827_, sizeof(void*)*1, v___x_826_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_830_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__9, &l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9);
v___x_831_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__10));
v___x_832_ = lean_box(0);
lean_inc(v___x_728_);
v___x_833_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_833_, 0, v___x_827_);
lean_ctor_set(v___x_833_, 1, v___x_728_);
lean_ctor_set(v___x_833_, 2, v___x_830_);
lean_ctor_set(v___x_833_, 3, v___x_831_);
lean_ctor_set(v___x_833_, 4, v___x_832_);
lean_ctor_set(v___x_833_, 5, v___x_828_);
lean_ctor_set(v___x_833_, 6, v___x_832_);
v___x_834_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*7, v___x_834_);
v___x_835_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*7 + 1, v___x_835_);
v___x_836_ = lean_unbox(v_a_812_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*7 + 2, v___x_836_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*7 + 3, v___x_814_);
v___x_837_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__11, &l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11);
v___x_838_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__12, &l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12);
v___x_839_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__13, &l_Lean_Meta_mkSimpAttr___lam__0___closed__13_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13);
v___x_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_840_, 0, v___x_837_);
lean_ctor_set(v___x_840_, 1, v___x_838_);
lean_ctor_set(v___x_840_, 2, v___x_728_);
lean_ctor_set(v___x_840_, 3, v___x_829_);
lean_ctor_set(v___x_840_, 4, v___x_839_);
v___x_841_ = lean_st_mk_ref(v___x_840_);
v___x_842_ = lean_unbox(v_a_812_);
lean_inc(v_declName_730_);
v___x_843_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_declName_730_, v___x_842_, v___x_833_, v___x_841_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = lean_box(0);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = l_Lean_Syntax_getArg(v_stx_731_, v___x_846_);
v___x_848_ = l_Lean_Syntax_isNone(v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; uint8_t v___x_853_; 
v___x_849_ = l_Lean_Syntax_getArg(v___x_847_, v___x_828_);
lean_dec(v___x_847_);
v___x_850_ = l_Lean_Syntax_getKind(v___x_849_);
v___x_851_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__15));
v___x_852_ = lean_name_eq(v___x_850_, v___x_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_unbox(v_a_812_);
lean_dec(v_a_812_);
v___y_800_ = v___x_833_;
v___y_801_ = v___x_845_;
v___y_802_ = v_a_844_;
v___y_803_ = v___x_841_;
v___y_804_ = v___x_853_;
v___y_805_ = v___x_814_;
v___y_806_ = v___x_852_;
goto v___jp_799_;
}
else
{
uint8_t v___x_854_; 
lean_dec(v___x_847_);
v___x_854_ = lean_unbox(v_a_812_);
lean_dec(v_a_812_);
v___y_800_ = v___x_833_;
v___y_801_ = v___x_845_;
v___y_802_ = v_a_844_;
v___y_803_ = v___x_841_;
v___y_804_ = v___x_854_;
v___y_805_ = v___x_814_;
v___y_806_ = v___x_814_;
goto v___jp_799_;
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v___x_841_);
lean_dec_ref_known(v___x_833_, 7);
lean_dec(v_a_812_);
lean_dec(v_stx_731_);
lean_dec(v_declName_730_);
lean_dec_ref(v_ext_727_);
v_a_855_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_843_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_843_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_a_812_);
lean_dec(v___x_728_);
lean_dec_ref(v_ext_727_);
v___x_863_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_729_);
v___x_864_ = l_Lean_Attribute_add(v_declName_730_, v___x_863_, v_stx_731_, v_attrKind_732_, v___y_733_, v___y_734_);
return v___x_864_;
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_stx_731_);
lean_dec(v_declName_730_);
lean_dec(v_attrName_729_);
lean_dec(v___x_728_);
lean_dec_ref(v_ext_727_);
v_a_865_ = lean_ctor_get(v___y_811_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___y_811_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___y_811_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object* v_ext_877_, lean_object* v___x_878_, lean_object* v_attrName_879_, lean_object* v_declName_880_, lean_object* v_stx_881_, lean_object* v_attrKind_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v_attrKind_boxed_886_; lean_object* v_res_887_; 
v_attrKind_boxed_886_ = lean_unbox(v_attrKind_882_);
v_res_887_ = l_Lean_Meta_mkSimpAttr___lam__0(v_ext_877_, v___x_878_, v_attrName_879_, v_declName_880_, v_stx_881_, v_attrKind_boxed_886_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
lean_inc_ref(v_a_888_);
return v_a_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object* v_a_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Meta_mkSimpAttr___lam__1(v_a_890_, v_x_891_);
lean_dec_ref(v_x_891_);
lean_dec_ref(v_a_890_);
return v_res_892_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_keys_893_, lean_object* v_i_894_, lean_object* v_k_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_array_get_size(v_keys_893_);
v___x_897_ = lean_nat_dec_lt(v_i_894_, v___x_896_);
if (v___x_897_ == 0)
{
lean_dec(v_i_894_);
return v___x_897_;
}
else
{
lean_object* v_k_x27_898_; uint8_t v___x_899_; 
v_k_x27_898_ = lean_array_fget_borrowed(v_keys_893_, v_i_894_);
v___x_899_ = lean_name_eq(v_k_895_, v_k_x27_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_i_894_, v___x_900_);
lean_dec(v_i_894_);
v_i_894_ = v___x_901_;
goto _start;
}
else
{
lean_dec(v_i_894_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_keys_903_, lean_object* v_i_904_, lean_object* v_k_905_){
_start:
{
uint8_t v_res_906_; lean_object* v_r_907_; 
v_res_906_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_903_, v_i_904_, v_k_905_);
lean_dec(v_k_905_);
lean_dec_ref(v_keys_903_);
v_r_907_ = lean_box(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(lean_object* v_x_908_, size_t v_x_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v_es_911_; lean_object* v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v_j_915_; lean_object* v___x_916_; 
v_es_911_ = lean_ctor_get(v_x_908_, 0);
v___x_912_ = lean_box(2);
v___x_913_ = ((size_t)31ULL);
v___x_914_ = lean_usize_land(v_x_909_, v___x_913_);
v_j_915_ = lean_usize_to_nat(v___x_914_);
v___x_916_ = lean_array_get_borrowed(v___x_912_, v_es_911_, v_j_915_);
lean_dec(v_j_915_);
switch(lean_obj_tag(v___x_916_))
{
case 0:
{
lean_object* v_key_917_; uint8_t v___x_918_; 
v_key_917_ = lean_ctor_get(v___x_916_, 0);
v___x_918_ = lean_name_eq(v_x_910_, v_key_917_);
return v___x_918_;
}
case 1:
{
lean_object* v_node_919_; size_t v___x_920_; size_t v___x_921_; 
v_node_919_ = lean_ctor_get(v___x_916_, 0);
v___x_920_ = ((size_t)5ULL);
v___x_921_ = lean_usize_shift_right(v_x_909_, v___x_920_);
v_x_908_ = v_node_919_;
v_x_909_ = v___x_921_;
goto _start;
}
default: 
{
uint8_t v___x_923_; 
v___x_923_ = 0;
return v___x_923_;
}
}
}
else
{
lean_object* v_ks_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_ks_924_ = lean_ctor_get(v_x_908_, 0);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_ks_924_, v___x_925_, v_x_910_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
size_t v_x_8460__boxed_930_; uint8_t v_res_931_; lean_object* v_r_932_; 
v_x_8460__boxed_930_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_res_931_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_927_, v_x_8460__boxed_930_, v_x_929_);
lean_dec(v_x_929_);
lean_dec_ref(v_x_927_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
uint64_t v___y_936_; 
if (lean_obj_tag(v_x_934_) == 0)
{
uint64_t v___x_939_; 
v___x_939_ = 1723ULL;
v___y_936_ = v___x_939_;
goto v___jp_935_;
}
else
{
uint64_t v_hash_940_; 
v_hash_940_ = lean_ctor_get_uint64(v_x_934_, sizeof(void*)*2);
v___y_936_ = v_hash_940_;
goto v___jp_935_;
}
v___jp_935_:
{
size_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_uint64_to_usize(v___y_936_);
v___x_938_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_933_, v___x_937_, v_x_934_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___boxed(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_941_, v_x_942_);
lean_dec(v_x_942_);
lean_dec_ref(v_x_941_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_msgData_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_env_950_; lean_object* v_options_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_949_ = lean_st_ref_get(v___y_947_);
v_env_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_950_);
lean_dec(v___x_949_);
v_options_951_ = lean_ctor_get(v___y_946_, 1);
v___x_952_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
v___x_953_ = lean_unsigned_to_nat(32u);
v___x_954_ = lean_mk_empty_array_with_capacity(v___x_953_);
lean_dec_ref(v___x_954_);
v___x_955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5);
lean_inc_ref(v_options_951_);
v___x_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_956_, 0, v_env_950_);
lean_ctor_set(v___x_956_, 1, v___x_952_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v_options_951_);
v___x_957_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_msgData_945_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_msgData_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v_msgData_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_963_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(uint8_t v_suppressElabErrors_971_, uint8_t v___y_972_, lean_object* v_x_973_){
_start:
{
if (lean_obj_tag(v_x_973_) == 1)
{
lean_object* v_pre_974_; 
v_pre_974_ = lean_ctor_get(v_x_973_, 0);
switch(lean_obj_tag(v_pre_974_))
{
case 1:
{
lean_object* v_pre_975_; 
v_pre_975_ = lean_ctor_get(v_pre_974_, 0);
switch(lean_obj_tag(v_pre_975_))
{
case 0:
{
lean_object* v_str_976_; lean_object* v_str_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_str_976_ = lean_ctor_get(v_x_973_, 1);
v_str_977_ = lean_ctor_get(v_pre_974_, 1);
v___x_978_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0));
v___x_979_ = lean_string_dec_eq(v_str_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__2));
v___x_981_ = lean_string_dec_eq(v_str_977_, v___x_980_);
if (v___x_981_ == 0)
{
return v___x_981_;
}
else
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1));
v___x_983_ = lean_string_dec_eq(v_str_976_, v___x_982_);
if (v___x_983_ == 0)
{
return v___x_983_;
}
else
{
return v_suppressElabErrors_971_;
}
}
}
else
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2));
v___x_985_ = lean_string_dec_eq(v_str_976_, v___x_984_);
if (v___x_985_ == 0)
{
return v___x_985_;
}
else
{
return v_suppressElabErrors_971_;
}
}
}
case 1:
{
lean_object* v_pre_986_; 
v_pre_986_ = lean_ctor_get(v_pre_975_, 0);
if (lean_obj_tag(v_pre_986_) == 0)
{
lean_object* v_str_987_; lean_object* v_str_988_; lean_object* v_str_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_str_987_ = lean_ctor_get(v_x_973_, 1);
v_str_988_ = lean_ctor_get(v_pre_974_, 1);
v_str_989_ = lean_ctor_get(v_pre_975_, 1);
v___x_990_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3));
v___x_991_ = lean_string_dec_eq(v_str_989_, v___x_990_);
if (v___x_991_ == 0)
{
return v___x_991_;
}
else
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4));
v___x_993_ = lean_string_dec_eq(v_str_988_, v___x_992_);
if (v___x_993_ == 0)
{
return v___x_993_;
}
else
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5));
v___x_995_ = lean_string_dec_eq(v_str_987_, v___x_994_);
if (v___x_995_ == 0)
{
return v___x_995_;
}
else
{
return v_suppressElabErrors_971_;
}
}
}
}
else
{
return v___y_972_;
}
}
default: 
{
return v___y_972_;
}
}
}
case 0:
{
lean_object* v_str_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_str_996_ = lean_ctor_get(v_x_973_, 1);
v___x_997_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6));
v___x_998_ = lean_string_dec_eq(v_str_996_, v___x_997_);
if (v___x_998_ == 0)
{
return v___x_998_;
}
else
{
return v_suppressElabErrors_971_;
}
}
default: 
{
return v___y_972_;
}
}
}
else
{
return v___y_972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_999_, lean_object* v___y_1000_, lean_object* v_x_1001_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1002_; uint8_t v___y_8592__boxed_1003_; uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_suppressElabErrors_boxed_1002_ = lean_unbox(v_suppressElabErrors_999_);
v___y_8592__boxed_1003_ = lean_unbox(v___y_1000_);
v_res_1004_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(v_suppressElabErrors_boxed_1002_, v___y_8592__boxed_1003_, v_x_1001_);
lean_dec(v_x_1001_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(lean_object* v_opts_1006_, lean_object* v_opt_1007_){
_start:
{
lean_object* v_name_1008_; lean_object* v_defValue_1009_; lean_object* v_map_1010_; lean_object* v___x_1011_; 
v_name_1008_ = lean_ctor_get(v_opt_1007_, 0);
v_defValue_1009_ = lean_ctor_get(v_opt_1007_, 1);
v_map_1010_ = lean_ctor_get(v_opts_1006_, 0);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1010_, v_name_1008_);
if (lean_obj_tag(v___x_1011_) == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_unbox(v_defValue_1009_);
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; 
v_val_1013_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v___x_1011_, 1);
if (lean_obj_tag(v_val_1013_) == 1)
{
uint8_t v_v_1014_; 
v_v_1014_ = lean_ctor_get_uint8(v_val_1013_, 0);
lean_dec_ref_known(v_val_1013_, 0);
return v_v_1014_;
}
else
{
uint8_t v___x_1015_; 
lean_dec(v_val_1013_);
v___x_1015_ = lean_unbox(v_defValue_1009_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11___boxed(lean_object* v_opts_1016_, lean_object* v_opt_1017_){
_start:
{
uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_res_1018_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_opts_1016_, v_opt_1017_);
lean_dec_ref(v_opt_1017_);
lean_dec_ref(v_opts_1016_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(lean_object* v_ref_1021_, lean_object* v_msgData_1022_, uint8_t v_severity_1023_, uint8_t v_isSilent_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___y_1029_; uint8_t v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1065_; uint8_t v___y_1066_; uint8_t v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; uint8_t v___y_1095_; uint8_t v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1101_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; uint8_t v___y_1106_; uint8_t v___x_1111_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; uint8_t v___y_1117_; uint8_t v___y_1118_; uint8_t v___y_1120_; uint8_t v___x_1134_; 
v___x_1111_ = 2;
v___x_1134_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1023_, v___x_1111_);
if (v___x_1134_ == 0)
{
v___y_1120_ = v___x_1134_;
goto v___jp_1119_;
}
else
{
uint8_t v___x_1135_; 
lean_inc_ref(v_msgData_1022_);
v___x_1135_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1022_);
v___y_1120_ = v___x_1135_;
goto v___jp_1119_;
}
v___jp_1028_:
{
lean_object* v___x_1038_; lean_object* v_currNamespace_1039_; lean_object* v_openDecls_1040_; lean_object* v_env_1041_; lean_object* v_nextMacroScope_1042_; lean_object* v_ngen_1043_; lean_object* v_auxDeclNGen_1044_; lean_object* v_traceState_1045_; lean_object* v_cache_1046_; lean_object* v_messages_1047_; lean_object* v_infoState_1048_; lean_object* v_snapshotTasks_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1063_; 
v___x_1038_ = lean_st_ref_take(v___y_1037_);
v_currNamespace_1039_ = lean_ctor_get(v___y_1036_, 5);
v_openDecls_1040_ = lean_ctor_get(v___y_1036_, 6);
v_env_1041_ = lean_ctor_get(v___x_1038_, 0);
v_nextMacroScope_1042_ = lean_ctor_get(v___x_1038_, 1);
v_ngen_1043_ = lean_ctor_get(v___x_1038_, 2);
v_auxDeclNGen_1044_ = lean_ctor_get(v___x_1038_, 3);
v_traceState_1045_ = lean_ctor_get(v___x_1038_, 4);
v_cache_1046_ = lean_ctor_get(v___x_1038_, 5);
v_messages_1047_ = lean_ctor_get(v___x_1038_, 6);
v_infoState_1048_ = lean_ctor_get(v___x_1038_, 7);
v_snapshotTasks_1049_ = lean_ctor_get(v___x_1038_, 8);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1051_ = v___x_1038_;
v_isShared_1052_ = v_isSharedCheck_1063_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snapshotTasks_1049_);
lean_inc(v_infoState_1048_);
lean_inc(v_messages_1047_);
lean_inc(v_cache_1046_);
lean_inc(v_traceState_1045_);
lean_inc(v_auxDeclNGen_1044_);
lean_inc(v_ngen_1043_);
lean_inc(v_nextMacroScope_1042_);
lean_inc(v_env_1041_);
lean_dec(v___x_1038_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1063_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_inc(v_openDecls_1040_);
lean_inc(v_currNamespace_1039_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_currNamespace_1039_);
lean_ctor_set(v___x_1053_, 1, v_openDecls_1040_);
v___x_1054_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___y_1031_);
lean_inc_ref(v___y_1034_);
lean_inc_ref(v___y_1032_);
v___x_1055_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1055_, 0, v___y_1032_);
lean_ctor_set(v___x_1055_, 1, v___y_1035_);
lean_ctor_set(v___x_1055_, 2, v___y_1029_);
lean_ctor_set(v___x_1055_, 3, v___y_1034_);
lean_ctor_set(v___x_1055_, 4, v___x_1054_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*5, v___y_1033_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*5 + 1, v___y_1030_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*5 + 2, v_isSilent_1024_);
v___x_1056_ = l_Lean_MessageLog_add(v___x_1055_, v_messages_1047_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 6, v___x_1056_);
v___x_1058_ = v___x_1051_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_env_1041_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_nextMacroScope_1042_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_ngen_1043_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_auxDeclNGen_1044_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_traceState_1045_);
lean_ctor_set(v_reuseFailAlloc_1062_, 5, v_cache_1046_);
lean_ctor_set(v_reuseFailAlloc_1062_, 6, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1062_, 7, v_infoState_1048_);
lean_ctor_set(v_reuseFailAlloc_1062_, 8, v_snapshotTasks_1049_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_st_ref_put(v___y_1037_, v___x_1058_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
v___jp_1064_:
{
lean_object* v_fileName_1072_; lean_object* v_fileMap_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1089_; 
v_fileName_1072_ = lean_ctor_get(v___y_1069_, 0);
v_fileMap_1073_ = lean_ctor_get(v___y_1069_, 1);
v___x_1074_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1022_);
v___x_1075_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v___x_1074_, v___y_1025_, v___y_1026_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1089_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1089_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_inc_ref_n(v_fileMap_1073_, 2);
v___x_1080_ = l_Lean_FileMap_toPosition(v_fileMap_1073_, v___y_1068_);
lean_dec(v___y_1068_);
v___x_1081_ = l_Lean_FileMap_toPosition(v_fileMap_1073_, v___y_1071_);
lean_dec(v___y_1071_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0));
if (v___y_1066_ == 0)
{
lean_del_object(v___x_1078_);
lean_dec_ref(v___y_1065_);
v___y_1029_ = v___x_1082_;
v___y_1030_ = v___y_1067_;
v___y_1031_ = v_a_1076_;
v___y_1032_ = v_fileName_1072_;
v___y_1033_ = v___y_1070_;
v___y_1034_ = v___x_1083_;
v___y_1035_ = v___x_1080_;
v___y_1036_ = v___y_1025_;
v___y_1037_ = v___y_1026_;
goto v___jp_1028_;
}
else
{
uint8_t v___x_1084_; 
lean_inc(v_a_1076_);
v___x_1084_ = l_Lean_MessageData_hasTag(v___y_1065_, v_a_1076_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec_ref_known(v___x_1082_, 1);
lean_dec_ref(v___x_1080_);
lean_dec(v_a_1076_);
v___x_1085_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1085_);
v___x_1087_ = v___x_1078_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_del_object(v___x_1078_);
v___y_1029_ = v___x_1082_;
v___y_1030_ = v___y_1067_;
v___y_1031_ = v_a_1076_;
v___y_1032_ = v_fileName_1072_;
v___y_1033_ = v___y_1070_;
v___y_1034_ = v___x_1083_;
v___y_1035_ = v___x_1080_;
v___y_1036_ = v___y_1025_;
v___y_1037_ = v___y_1026_;
goto v___jp_1028_;
}
}
}
}
v___jp_1090_:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Syntax_getTailPos_x3f(v___y_1093_, v___y_1096_);
lean_dec(v___y_1093_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_inc(v___y_1097_);
v___y_1065_ = v___y_1091_;
v___y_1066_ = v___y_1092_;
v___y_1067_ = v___y_1095_;
v___y_1068_ = v___y_1097_;
v___y_1069_ = v___y_1094_;
v___y_1070_ = v___y_1096_;
v___y_1071_ = v___y_1097_;
goto v___jp_1064_;
}
else
{
lean_object* v_val_1099_; 
v_val_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___y_1065_ = v___y_1091_;
v___y_1066_ = v___y_1092_;
v___y_1067_ = v___y_1095_;
v___y_1068_ = v___y_1097_;
v___y_1069_ = v___y_1094_;
v___y_1070_ = v___y_1096_;
v___y_1071_ = v_val_1099_;
goto v___jp_1064_;
}
}
v___jp_1100_:
{
lean_object* v_ref_1107_; lean_object* v___x_1108_; 
v_ref_1107_ = l_Lean_replaceRef(v_ref_1021_, v___y_1103_);
v___x_1108_ = l_Lean_Syntax_getPos_x3f(v_ref_1107_, v___y_1105_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___y_1091_ = v___y_1101_;
v___y_1092_ = v___y_1102_;
v___y_1093_ = v_ref_1107_;
v___y_1094_ = v___y_1104_;
v___y_1095_ = v___y_1106_;
v___y_1096_ = v___y_1105_;
v___y_1097_ = v___x_1109_;
goto v___jp_1090_;
}
else
{
lean_object* v_val_1110_; 
v_val_1110_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v___x_1108_, 1);
v___y_1091_ = v___y_1101_;
v___y_1092_ = v___y_1102_;
v___y_1093_ = v_ref_1107_;
v___y_1094_ = v___y_1104_;
v___y_1095_ = v___y_1106_;
v___y_1096_ = v___y_1105_;
v___y_1097_ = v_val_1110_;
goto v___jp_1090_;
}
}
v___jp_1112_:
{
if (v___y_1118_ == 0)
{
v___y_1101_ = v___y_1115_;
v___y_1102_ = v___y_1113_;
v___y_1103_ = v___y_1114_;
v___y_1104_ = v___y_1116_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v_severity_1023_;
goto v___jp_1100_;
}
else
{
v___y_1101_ = v___y_1115_;
v___y_1102_ = v___y_1113_;
v___y_1103_ = v___y_1114_;
v___y_1104_ = v___y_1116_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___x_1111_;
goto v___jp_1100_;
}
}
v___jp_1119_:
{
if (v___y_1120_ == 0)
{
lean_object* v_toCold_1121_; lean_object* v_options_1122_; lean_object* v_ref_1123_; uint8_t v_suppressElabErrors_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___f_1127_; uint8_t v___x_1128_; uint8_t v___x_1129_; 
v_toCold_1121_ = lean_ctor_get(v___y_1025_, 0);
v_options_1122_ = lean_ctor_get(v___y_1025_, 1);
v_ref_1123_ = lean_ctor_get(v___y_1025_, 4);
v_suppressElabErrors_1124_ = lean_ctor_get_uint8(v___y_1025_, sizeof(void*)*10 + 1);
v___x_1125_ = lean_box(v_suppressElabErrors_1124_);
v___x_1126_ = lean_box(v___y_1120_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1127_, 0, v___x_1125_);
lean_closure_set(v___f_1127_, 1, v___x_1126_);
v___x_1128_ = 1;
v___x_1129_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1023_, v___x_1128_);
if (v___x_1129_ == 0)
{
v___y_1113_ = v_suppressElabErrors_1124_;
v___y_1114_ = v_ref_1123_;
v___y_1115_ = v___f_1127_;
v___y_1116_ = v_toCold_1121_;
v___y_1117_ = v___y_1120_;
v___y_1118_ = v___x_1129_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = l_Lean_warningAsError;
v___x_1131_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_options_1122_, v___x_1130_);
v___y_1113_ = v_suppressElabErrors_1124_;
v___y_1114_ = v_ref_1123_;
v___y_1115_ = v___f_1127_;
v___y_1116_ = v_toCold_1121_;
v___y_1117_ = v___y_1120_;
v___y_1118_ = v___x_1131_;
goto v___jp_1112_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref(v_msgData_1022_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_1136_, lean_object* v_msgData_1137_, lean_object* v_severity_1138_, lean_object* v_isSilent_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_severity_boxed_1143_; uint8_t v_isSilent_boxed_1144_; lean_object* v_res_1145_; 
v_severity_boxed_1143_ = lean_unbox(v_severity_1138_);
v_isSilent_boxed_1144_ = lean_unbox(v_isSilent_1139_);
v_res_1145_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1136_, v_msgData_1137_, v_severity_boxed_1143_, v_isSilent_boxed_1144_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1136_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(lean_object* v_msgData_1146_, uint8_t v_severity_1147_, uint8_t v_isSilent_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_ref_1152_; lean_object* v___x_1153_; 
v_ref_1152_ = lean_ctor_get(v___y_1149_, 4);
v___x_1153_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1152_, v_msgData_1146_, v_severity_1147_, v_isSilent_1148_, v___y_1149_, v___y_1150_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1154_, lean_object* v_severity_1155_, lean_object* v_isSilent_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
uint8_t v_severity_boxed_1160_; uint8_t v_isSilent_boxed_1161_; lean_object* v_res_1162_; 
v_severity_boxed_1160_ = lean_unbox(v_severity_1155_);
v_isSilent_boxed_1161_ = lean_unbox(v_isSilent_1156_);
v_res_1162_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1154_, v_severity_boxed_1160_, v_isSilent_boxed_1161_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(lean_object* v_msgData_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = 1;
v___x_1168_ = 0;
v___x_1169_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1163_, v___x_1167_, v___x_1168_, v___y_1164_, v___y_1165_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2___boxed(lean_object* v_msgData_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v_msgData_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1174_;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object* v_d_1178_, lean_object* v_thmId_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___y_1208_; uint8_t v___x_1222_; 
v___x_1222_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1178_, v_thmId_1179_);
if (v___x_1222_ == 0)
{
if (lean_obj_tag(v_thmId_1179_) == 0)
{
lean_object* v_declName_1223_; uint8_t v___x_1224_; 
v_declName_1223_ = lean_ctor_get(v_thmId_1179_, 0);
v___x_1224_ = l_Lean_Meta_SimpTheorems_isDeclToUnfold(v_d_1178_, v_declName_1223_);
if (v___x_1224_ == 0)
{
lean_object* v_toUnfoldThms_1225_; uint8_t v___x_1226_; 
v_toUnfoldThms_1225_ = lean_ctor_get(v_d_1178_, 5);
v___x_1226_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_toUnfoldThms_1225_, v_declName_1223_);
v___y_1208_ = v___x_1226_;
goto v___jp_1207_;
}
else
{
v___y_1208_ = v___x_1224_;
goto v___jp_1207_;
}
}
else
{
v___y_1208_ = v___x_1222_;
goto v___jp_1207_;
}
}
else
{
v___y_1208_ = v___x_1222_;
goto v___jp_1207_;
}
v___jp_1183_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1184_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1185_ = l_Lean_Meta_Origin_key(v_thmId_1179_);
lean_dec_ref(v_thmId_1179_);
v___x_1186_ = l_Lean_MessageData_ofName(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1184_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_obj_once(&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1, &l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once, _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v___x_1189_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1190_, 0);
lean_dec(v_unused_1198_);
v___x_1192_ = v___x_1190_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1190_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_d_1178_);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_d_1178_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_d_1178_);
v_a_1199_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1190_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
v___jp_1207_:
{
if (v___y_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_inc_ref(v_thmId_1179_);
v___x_1209_ = l_Lean_Meta_Origin_converse(v_thmId_1179_);
if (lean_obj_tag(v___x_1209_) == 1)
{
lean_object* v_val_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1219_; 
v_val_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_val_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
uint8_t v___x_1214_; 
v___x_1214_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1178_, v_val_1210_);
if (v___x_1214_ == 0)
{
lean_del_object(v___x_1212_);
lean_dec(v_val_1210_);
goto v___jp_1183_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec_ref(v_thmId_1179_);
v___x_1215_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1178_, v_val_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1215_);
v___x_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_dec(v___x_1209_);
goto v___jp_1183_;
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1178_, v_thmId_1179_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object* v_d_1227_, lean_object* v_thmId_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v_d_1227_, v_thmId_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object* v_ext_1233_, lean_object* v___x_1234_, lean_object* v_attrName_1235_, lean_object* v_declName_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___y_1241_; lean_object* v___x_1302_; 
lean_inc(v_declName_1236_);
v___x_1302_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_1236_, v___y_1238_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; uint8_t v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
v___x_1304_ = lean_unbox(v_a_1303_);
lean_dec(v_a_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref_known(v___x_1302_, 1);
v___x_1305_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_1236_, v___y_1238_);
v___y_1241_ = v___x_1305_;
goto v___jp_1240_;
}
else
{
v___y_1241_ = v___x_1302_;
goto v___jp_1240_;
}
}
else
{
v___y_1241_ = v___x_1302_;
goto v___jp_1240_;
}
v___jp_1240_:
{
if (lean_obj_tag(v___y_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___y_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___y_1241_, 1);
v___x_1243_ = lean_unbox(v_a_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v_ext_1245_; lean_object* v_toEnvExtension_1246_; lean_object* v_env_1247_; lean_object* v_asyncMode_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_attrName_1235_);
v___x_1244_ = lean_st_ref_get(v___y_1238_);
v_ext_1245_ = lean_ctor_get(v_ext_1233_, 1);
v_toEnvExtension_1246_ = lean_ctor_get(v_ext_1245_, 0);
v_env_1247_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_env_1247_);
lean_dec(v___x_1244_);
v_asyncMode_1248_ = lean_ctor_get(v_toEnvExtension_1246_, 2);
v___x_1249_ = 1;
v___x_1250_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1234_, v_ext_1233_, v_env_1247_, v_asyncMode_1248_);
v___x_1251_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1251_, 0, v_declName_1236_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1249_);
v___x_1252_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1 + 1, v___x_1252_);
v___x_1253_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v___x_1250_, v___x_1251_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1283_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1283_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1283_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v_env_1259_; lean_object* v_nextMacroScope_1260_; lean_object* v_ngen_1261_; lean_object* v_auxDeclNGen_1262_; lean_object* v_traceState_1263_; lean_object* v_messages_1264_; lean_object* v_infoState_1265_; lean_object* v_snapshotTasks_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1281_; 
v___x_1258_ = lean_st_ref_take(v___y_1238_);
v_env_1259_ = lean_ctor_get(v___x_1258_, 0);
v_nextMacroScope_1260_ = lean_ctor_get(v___x_1258_, 1);
v_ngen_1261_ = lean_ctor_get(v___x_1258_, 2);
v_auxDeclNGen_1262_ = lean_ctor_get(v___x_1258_, 3);
v_traceState_1263_ = lean_ctor_get(v___x_1258_, 4);
v_messages_1264_ = lean_ctor_get(v___x_1258_, 6);
v_infoState_1265_ = lean_ctor_get(v___x_1258_, 7);
v_snapshotTasks_1266_ = lean_ctor_get(v___x_1258_, 8);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1258_, 5);
lean_dec(v_unused_1282_);
v___x_1268_ = v___x_1258_;
v_isShared_1269_ = v_isSharedCheck_1281_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snapshotTasks_1266_);
lean_inc(v_infoState_1265_);
lean_inc(v_messages_1264_);
lean_inc(v_traceState_1263_);
lean_inc(v_auxDeclNGen_1262_);
lean_inc(v_ngen_1261_);
lean_inc(v_nextMacroScope_1260_);
lean_inc(v_env_1259_);
lean_dec(v___x_1258_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1281_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1270_, 0, v_a_1254_);
v___x_1271_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1233_, v_env_1259_, v___f_1270_);
v___x_1272_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 5, v___x_1272_);
lean_ctor_set(v___x_1268_, 0, v___x_1271_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_nextMacroScope_1260_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_ngen_1261_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_auxDeclNGen_1262_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_traceState_1263_);
lean_ctor_set(v_reuseFailAlloc_1280_, 5, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1280_, 6, v_messages_1264_);
lean_ctor_set(v_reuseFailAlloc_1280_, 7, v_infoState_1265_);
lean_ctor_set(v_reuseFailAlloc_1280_, 8, v_snapshotTasks_1266_);
v___x_1274_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_st_ref_put(v___y_1238_, v___x_1274_);
v___x_1276_ = lean_box(0);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1276_);
v___x_1278_ = v___x_1256_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_ext_1233_);
v_a_1284_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1253_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1253_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec(v_a_1242_);
lean_dec_ref(v_ext_1233_);
v___x_1292_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_1235_);
v___x_1293_ = l_Lean_Attribute_erase(v_declName_1236_, v___x_1292_, v___y_1237_, v___y_1238_);
return v___x_1293_;
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_declName_1236_);
lean_dec(v_attrName_1235_);
lean_dec_ref(v_ext_1233_);
v_a_1294_ = lean_ctor_get(v___y_1241_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___y_1241_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___y_1241_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___y_1241_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object* v_ext_1306_, lean_object* v___x_1307_, lean_object* v_attrName_1308_, lean_object* v_declName_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Meta_mkSimpAttr___lam__2(v_ext_1306_, v___x_1307_, v_attrName_1308_, v_declName_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v___x_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* v_attrName_1314_, lean_object* v_attrDescr_1315_, lean_object* v_ext_1316_, lean_object* v_ref_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1319_ = lean_box(1);
lean_inc_n(v_attrName_1314_, 2);
lean_inc_ref(v_ext_1316_);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1320_, 0, v_ext_1316_);
lean_closure_set(v___f_1320_, 1, v___x_1319_);
lean_closure_set(v___f_1320_, 2, v_attrName_1314_);
v___x_1321_ = l_Lean_Meta_instInhabitedSimpTheorems_default;
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1322_, 0, v_ext_1316_);
lean_closure_set(v___f_1322_, 1, v___x_1321_);
lean_closure_set(v___f_1322_, 2, v_attrName_1314_);
v___x_1323_ = 1;
v___x_1324_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1324_, 0, v_ref_1317_);
lean_ctor_set(v___x_1324_, 1, v_attrName_1314_);
lean_ctor_set(v___x_1324_, 2, v_attrDescr_1315_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*3, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___f_1320_);
lean_ctor_set(v___x_1325_, 2, v___f_1322_);
v___x_1326_ = l_Lean_registerBuiltinAttribute(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___boxed(lean_object* v_attrName_1327_, lean_object* v_attrDescr_1328_, lean_object* v_ext_1329_, lean_object* v_ref_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_mkSimpAttr(v_attrName_1327_, v_attrDescr_1328_, v_ext_1329_, v_ref_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(lean_object* v_00_u03b1_1333_, lean_object* v_constName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_constName_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(v_00_u03b1_1341_, v_constName_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_1350_, v_x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
uint8_t v_res_1356_; lean_object* v_r_1357_; 
v_res_1356_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(v_00_u03b2_1353_, v_x_1354_, v_x_1355_);
lean_dec(v_x_1355_);
lean_dec_ref(v_x_1354_);
v_r_1357_ = lean_box(v_res_1356_);
return v_r_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1358_, lean_object* v_ref_1359_, lean_object* v_constName_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1359_, v_constName_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_ref_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_1367_, v_ref_1368_, v_constName_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v_ref_1368_);
return v_res_1375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1376_, lean_object* v_x_1377_, size_t v_x_1378_, lean_object* v_x_1379_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_1377_, v_x_1378_, v_x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
size_t v_x_9192__boxed_1385_; uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_x_9192__boxed_1385_ = lean_unbox_usize(v_x_1383_);
lean_dec(v_x_1383_);
v_res_1386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(v_00_u03b2_1381_, v_x_1382_, v_x_9192__boxed_1385_, v_x_1384_);
lean_dec(v_x_1384_);
lean_dec_ref(v_x_1382_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1388_, lean_object* v_ref_1389_, lean_object* v_msg_1390_, lean_object* v_declHint_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1389_, v_msg_1390_, v_declHint_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1398_, lean_object* v_ref_1399_, lean_object* v_msg_1400_, lean_object* v_declHint_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1398_, v_ref_1399_, v_msg_1400_, v_declHint_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_ref_1399_);
return v_res_1407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1408_, lean_object* v_keys_1409_, lean_object* v_vals_1410_, lean_object* v_heq_1411_, lean_object* v_i_1412_, lean_object* v_k_1413_){
_start:
{
uint8_t v___x_1414_; 
v___x_1414_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_1409_, v_i_1412_, v_k_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1415_, lean_object* v_keys_1416_, lean_object* v_vals_1417_, lean_object* v_heq_1418_, lean_object* v_i_1419_, lean_object* v_k_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_1415_, v_keys_1416_, v_vals_1417_, v_heq_1418_, v_i_1419_, v_k_1420_);
lean_dec(v_k_1420_);
lean_dec_ref(v_vals_1417_);
lean_dec_ref(v_keys_1416_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(lean_object* v_msg_1423_, lean_object* v_declHint_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_1423_, v_declHint_1424_, v___y_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_msg_1431_, lean_object* v_declHint_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(v_msg_1431_, v_declHint_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b1_1439_, lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1440_, v_msg_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1448_, lean_object* v_ref_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_1448_, v_ref_1449_, v_msg_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v_ref_1449_);
return v_res_1456_;
}
}
static lean_object* _init_l_Lean_Meta_registerSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v_x_1460_){
_start:
{
if (lean_obj_tag(v_x_1460_) == 0)
{
lean_dec(v_b_1459_);
lean_dec(v_a_1458_);
return v_x_1460_;
}
else
{
lean_object* v_key_1461_; lean_object* v_value_1462_; lean_object* v_tail_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1475_; 
v_key_1461_ = lean_ctor_get(v_x_1460_, 0);
v_value_1462_ = lean_ctor_get(v_x_1460_, 1);
v_tail_1463_ = lean_ctor_get(v_x_1460_, 2);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_x_1460_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1465_ = v_x_1460_;
v_isShared_1466_ = v_isSharedCheck_1475_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_tail_1463_);
lean_inc(v_value_1462_);
lean_inc(v_key_1461_);
lean_dec(v_x_1460_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1475_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_name_eq(v_key_1461_, v_a_1458_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1458_, v_b_1459_, v_tail_1463_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 2, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_key_1461_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_value_1462_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v___x_1473_; 
lean_dec(v_value_1462_);
lean_dec(v_key_1461_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_b_1459_);
lean_ctor_set(v___x_1465_, 0, v_a_1458_);
v___x_1473_ = v___x_1465_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1458_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_b_1459_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_tail_1463_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
return v_x_1476_;
}
else
{
lean_object* v_key_1478_; lean_object* v_value_1479_; lean_object* v_tail_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1506_; 
v_key_1478_ = lean_ctor_get(v_x_1477_, 0);
v_value_1479_ = lean_ctor_get(v_x_1477_, 1);
v_tail_1480_ = lean_ctor_get(v_x_1477_, 2);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1477_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1482_ = v_x_1477_;
v_isShared_1483_ = v_isSharedCheck_1506_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_tail_1480_);
lean_inc(v_value_1479_);
lean_inc(v_key_1478_);
lean_dec(v_x_1477_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1506_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; uint64_t v___y_1486_; 
v___x_1484_ = lean_array_get_size(v_x_1476_);
if (lean_obj_tag(v_key_1478_) == 0)
{
uint64_t v___x_1504_; 
v___x_1504_ = 1723ULL;
v___y_1486_ = v___x_1504_;
goto v___jp_1485_;
}
else
{
uint64_t v_hash_1505_; 
v_hash_1505_ = lean_ctor_get_uint64(v_key_1478_, sizeof(void*)*2);
v___y_1486_ = v_hash_1505_;
goto v___jp_1485_;
}
v___jp_1485_:
{
uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v_fold_1489_; uint64_t v___x_1490_; uint64_t v___x_1491_; uint64_t v___x_1492_; size_t v___x_1493_; size_t v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1487_ = 32ULL;
v___x_1488_ = lean_uint64_shift_right(v___y_1486_, v___x_1487_);
v_fold_1489_ = lean_uint64_xor(v___y_1486_, v___x_1488_);
v___x_1490_ = 16ULL;
v___x_1491_ = lean_uint64_shift_right(v_fold_1489_, v___x_1490_);
v___x_1492_ = lean_uint64_xor(v_fold_1489_, v___x_1491_);
v___x_1493_ = lean_uint64_to_usize(v___x_1492_);
v___x_1494_ = lean_usize_of_nat(v___x_1484_);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_sub(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_usize_land(v___x_1493_, v___x_1496_);
v___x_1498_ = lean_array_uget_borrowed(v_x_1476_, v___x_1497_);
lean_inc(v___x_1498_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 2, v___x_1498_);
v___x_1500_ = v___x_1482_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_key_1478_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_value_1479_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_array_uset(v_x_1476_, v___x_1497_, v___x_1500_);
v_x_1476_ = v___x_1501_;
v_x_1477_ = v_tail_1480_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1507_, lean_object* v_source_1508_, lean_object* v_target_1509_){
_start:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_array_get_size(v_source_1508_);
v___x_1511_ = lean_nat_dec_lt(v_i_1507_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec_ref(v_source_1508_);
lean_dec(v_i_1507_);
return v_target_1509_;
}
else
{
lean_object* v_es_1512_; lean_object* v___x_1513_; lean_object* v_source_1514_; lean_object* v_target_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_es_1512_ = lean_array_fget(v_source_1508_, v_i_1507_);
v___x_1513_ = lean_box(0);
v_source_1514_ = lean_array_fset(v_source_1508_, v_i_1507_, v___x_1513_);
v_target_1515_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1509_, v_es_1512_);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_i_1507_, v___x_1516_);
lean_dec(v_i_1507_);
v_i_1507_ = v___x_1517_;
v_source_1508_ = v_source_1514_;
v_target_1509_ = v_target_1515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_nbuckets_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1520_ = lean_array_get_size(v_data_1519_);
v___x_1521_ = lean_unsigned_to_nat(2u);
v_nbuckets_1522_ = lean_nat_mul(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_mk_array(v_nbuckets_1522_, v___x_1524_);
v___x_1526_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_1523_, v_data_1519_, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_1527_, lean_object* v_x_1528_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = 0;
return v___x_1529_;
}
else
{
lean_object* v_key_1530_; lean_object* v_tail_1531_; uint8_t v___x_1532_; 
v_key_1530_ = lean_ctor_get(v_x_1528_, 0);
v_tail_1531_ = lean_ctor_get(v_x_1528_, 2);
v___x_1532_ = lean_name_eq(v_key_1530_, v_a_1527_);
if (v___x_1532_ == 0)
{
v_x_1528_ = v_tail_1531_;
goto _start;
}
else
{
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_1534_, lean_object* v_x_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1534_, v_x_1535_);
lean_dec(v_x_1535_);
lean_dec(v_a_1534_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(lean_object* v_m_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
lean_object* v_size_1541_; lean_object* v_buckets_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1588_; 
v_size_1541_ = lean_ctor_get(v_m_1538_, 0);
v_buckets_1542_ = lean_ctor_get(v_m_1538_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_m_1538_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1544_ = v_m_1538_;
v_isShared_1545_ = v_isSharedCheck_1588_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_buckets_1542_);
lean_inc(v_size_1541_);
lean_dec(v_m_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1588_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; uint64_t v___y_1548_; 
v___x_1546_ = lean_array_get_size(v_buckets_1542_);
if (lean_obj_tag(v_a_1539_) == 0)
{
uint64_t v___x_1586_; 
v___x_1586_ = 1723ULL;
v___y_1548_ = v___x_1586_;
goto v___jp_1547_;
}
else
{
uint64_t v_hash_1587_; 
v_hash_1587_ = lean_ctor_get_uint64(v_a_1539_, sizeof(void*)*2);
v___y_1548_ = v_hash_1587_;
goto v___jp_1547_;
}
v___jp_1547_:
{
uint64_t v___x_1549_; uint64_t v___x_1550_; uint64_t v_fold_1551_; uint64_t v___x_1552_; uint64_t v___x_1553_; uint64_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; lean_object* v_bkt_1560_; uint8_t v___x_1561_; 
v___x_1549_ = 32ULL;
v___x_1550_ = lean_uint64_shift_right(v___y_1548_, v___x_1549_);
v_fold_1551_ = lean_uint64_xor(v___y_1548_, v___x_1550_);
v___x_1552_ = 16ULL;
v___x_1553_ = lean_uint64_shift_right(v_fold_1551_, v___x_1552_);
v___x_1554_ = lean_uint64_xor(v_fold_1551_, v___x_1553_);
v___x_1555_ = lean_uint64_to_usize(v___x_1554_);
v___x_1556_ = lean_usize_of_nat(v___x_1546_);
v___x_1557_ = ((size_t)1ULL);
v___x_1558_ = lean_usize_sub(v___x_1556_, v___x_1557_);
v___x_1559_ = lean_usize_land(v___x_1555_, v___x_1558_);
v_bkt_1560_ = lean_array_uget_borrowed(v_buckets_1542_, v___x_1559_);
v___x_1561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1539_, v_bkt_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v_size_x27_1563_; lean_object* v___x_1564_; lean_object* v_buckets_x27_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1562_ = lean_unsigned_to_nat(1u);
v_size_x27_1563_ = lean_nat_add(v_size_1541_, v___x_1562_);
lean_dec(v_size_1541_);
lean_inc(v_bkt_1560_);
v___x_1564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1539_);
lean_ctor_set(v___x_1564_, 1, v_b_1540_);
lean_ctor_set(v___x_1564_, 2, v_bkt_1560_);
v_buckets_x27_1565_ = lean_array_uset(v_buckets_1542_, v___x_1559_, v___x_1564_);
v___x_1566_ = lean_unsigned_to_nat(4u);
v___x_1567_ = lean_nat_mul(v_size_x27_1563_, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(3u);
v___x_1569_ = lean_nat_div(v___x_1567_, v___x_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_array_get_size(v_buckets_x27_1565_);
v___x_1571_ = lean_nat_dec_le(v___x_1569_, v___x_1570_);
lean_dec(v___x_1569_);
if (v___x_1571_ == 0)
{
lean_object* v_val_1572_; lean_object* v___x_1574_; 
v_val_1572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_1565_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_val_1572_);
lean_ctor_set(v___x_1544_, 0, v_size_x27_1563_);
v___x_1574_ = v___x_1544_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_size_x27_1563_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_val_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
lean_object* v___x_1577_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_buckets_x27_1565_);
lean_ctor_set(v___x_1544_, 0, v_size_x27_1563_);
v___x_1577_ = v___x_1544_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_size_x27_1563_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_buckets_x27_1565_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v_buckets_x27_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_inc(v_bkt_1560_);
v___x_1579_ = lean_box(0);
v_buckets_x27_1580_ = lean_array_uset(v_buckets_1542_, v___x_1559_, v___x_1579_);
v___x_1581_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1539_, v_b_1540_, v_bkt_1560_);
v___x_1582_ = lean_array_uset(v_buckets_x27_1580_, v___x_1559_, v___x_1581_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___x_1582_);
v___x_1584_ = v___x_1544_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_size_1541_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* v_attrName_1589_, lean_object* v_attrDescr_1590_, lean_object* v_ref_1591_){
_start:
{
lean_object* v___x_1593_; 
lean_inc(v_ref_1591_);
v___x_1593_ = l_Lean_Meta_mkSimpExt(v_ref_1591_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_n(v_a_1594_, 2);
lean_dec_ref_known(v___x_1593_, 1);
lean_inc(v_attrName_1589_);
v___x_1595_ = l_Lean_Meta_mkSimpAttr(v_attrName_1589_, v_attrDescr_1590_, v_a_1594_, v_ref_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1595_, 0);
lean_dec(v_unused_1607_);
v___x_1597_ = v___x_1595_;
v_isShared_1598_ = v_isSharedCheck_1606_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v___x_1595_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1606_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1599_ = l_Lean_Meta_simpExtensionMapRef;
v___x_1600_ = lean_st_ref_take(v___x_1599_);
lean_inc(v_a_1594_);
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v___x_1600_, v_attrName_1589_, v_a_1594_);
v___x_1602_ = lean_st_ref_put(v___x_1599_, v___x_1601_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_a_1594_);
v___x_1604_ = v___x_1597_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1594_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1594_);
lean_dec(v_attrName_1589_);
v_a_1608_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1595_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1595_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_dec(v_ref_1591_);
lean_dec_ref(v_attrDescr_1590_);
lean_dec(v_attrName_1589_);
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___boxed(lean_object* v_attrName_1616_, lean_object* v_attrDescr_1617_, lean_object* v_ref_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_registerSimpAttr(v_attrName_1616_, v_attrDescr_1617_, v_ref_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(lean_object* v_00_u03b2_1621_, lean_object* v_m_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v_m_1622_, v_a_1623_, v_b_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_1626_, lean_object* v_a_1627_, lean_object* v_x_1628_){
_start:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1630_, lean_object* v_a_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(v_00_u03b2_1630_, v_a_1631_, v_x_1632_);
lean_dec(v_x_1632_);
lean_dec(v_a_1631_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_1635_, lean_object* v_data_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_data_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1639_, v_b_1640_, v_x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1643_, lean_object* v_i_1644_, lean_object* v_source_1645_, lean_object* v_target_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_1644_, v_source_1645_, v_target_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1649_, v_x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1666_ = l_Lean_Meta_registerSimpAttr(v___x_1663_, v___x_1664_, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1682_ = l_Lean_Meta_registerSimpAttr(v___x_1679_, v___x_1680_, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = l_Lean_Meta_simpExtension;
v___x_1688_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1687_, v_a_1685_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1689_);
lean_dec(v_a_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Meta_getSimpTheorems(v_a_1696_, v_a_1697_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = l_Lean_Meta_sevalSimpExtension;
v___x_1703_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1702_, v_a_1700_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1704_);
lean_dec(v_a_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_getSEvalTheorems(v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1724_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1724_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = ((lean_object*)(l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0));
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_mk_empty_array_with_capacity(v___x_1731_);
v___x_1733_ = lean_array_push(v___x_1732_, v_a_1727_);
v___x_1734_ = l_Lean_Options_empty;
v___x_1735_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1730_, v___x_1733_, v_a_1729_, v___x_1734_, v_a_1722_, v_a_1723_, v_a_1724_);
return v___x_1735_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1727_);
v_a_1736_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1728_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1728_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
v_a_1744_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1726_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1726_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1757_, v_a_1759_, v_a_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Meta_Simp_Context_mkDefault(v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1768_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
