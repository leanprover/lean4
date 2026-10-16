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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqConstantKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_ignoreEquations(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems_default;
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18;
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
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__1;
static const lean_array_object l_Lean_Meta_mkSimpAttr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Cannot add `simp` attribute to `"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`: It is not a proposition nor a definition (to unfold)"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = "The `[simp]` attribute can be added to lemmas that should be automatically used by the simplifier and to definitions that the simplifier should automatically unfold"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__11;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__14_value;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0___boxed(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(v_x_11_, v_x_12_);
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
v___x_15_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v_toCold_29_; lean_object* v_currNamespace_30_; lean_object* v___x_31_; lean_object* v_env_32_; lean_object* v_nextMacroScope_33_; lean_object* v_ngen_34_; lean_object* v_auxDeclNGen_35_; lean_object* v_traceState_36_; lean_object* v_recordedDeps_37_; lean_object* v_messages_38_; lean_object* v_infoState_39_; lean_object* v_snapshotTasks_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_67_; 
v_toCold_29_ = lean_ctor_get(v___y_26_, 0);
v_currNamespace_30_ = lean_ctor_get(v_toCold_29_, 4);
v___x_31_ = lean_st_ref_take(v___y_27_);
v_env_32_ = lean_ctor_get(v___x_31_, 0);
v_nextMacroScope_33_ = lean_ctor_get(v___x_31_, 1);
v_ngen_34_ = lean_ctor_get(v___x_31_, 2);
v_auxDeclNGen_35_ = lean_ctor_get(v___x_31_, 3);
v_traceState_36_ = lean_ctor_get(v___x_31_, 4);
v_recordedDeps_37_ = lean_ctor_get(v___x_31_, 6);
v_messages_38_ = lean_ctor_get(v___x_31_, 7);
v_infoState_39_ = lean_ctor_get(v___x_31_, 8);
v_snapshotTasks_40_ = lean_ctor_get(v___x_31_, 9);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v___x_31_, 5);
lean_dec(v_unused_68_);
v___x_42_ = v___x_31_;
v_isShared_43_ = v_isSharedCheck_67_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_snapshotTasks_40_);
lean_inc(v_infoState_39_);
lean_inc(v_messages_38_);
lean_inc(v_recordedDeps_37_);
lean_inc(v_traceState_36_);
lean_inc(v_auxDeclNGen_35_);
lean_inc(v_ngen_34_);
lean_inc(v_nextMacroScope_33_);
lean_inc(v_env_32_);
lean_dec(v___x_31_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_67_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
lean_inc(v_currNamespace_30_);
v___x_44_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_32_, v_ext_22_, v_b_23_, v_kind_24_, v_currNamespace_30_);
v___x_45_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 5, v___x_45_);
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_nextMacroScope_33_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v_ngen_34_);
lean_ctor_set(v_reuseFailAlloc_66_, 3, v_auxDeclNGen_35_);
lean_ctor_set(v_reuseFailAlloc_66_, 4, v_traceState_36_);
lean_ctor_set(v_reuseFailAlloc_66_, 5, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_66_, 6, v_recordedDeps_37_);
lean_ctor_set(v_reuseFailAlloc_66_, 7, v_messages_38_);
lean_ctor_set(v_reuseFailAlloc_66_, 8, v_infoState_39_);
lean_ctor_set(v_reuseFailAlloc_66_, 9, v_snapshotTasks_40_);
v___x_47_ = v_reuseFailAlloc_66_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v_mctx_50_; lean_object* v_zetaDeltaFVarIds_51_; lean_object* v_postponed_52_; lean_object* v_diag_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_64_; 
v___x_48_ = lean_st_ref_put(v___y_27_, v___x_47_);
v___x_49_ = lean_st_ref_take(v___y_25_);
v_mctx_50_ = lean_ctor_get(v___x_49_, 0);
v_zetaDeltaFVarIds_51_ = lean_ctor_get(v___x_49_, 2);
v_postponed_52_ = lean_ctor_get(v___x_49_, 3);
v_diag_53_ = lean_ctor_get(v___x_49_, 4);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_64_ == 0)
{
lean_object* v_unused_65_; 
v_unused_65_ = lean_ctor_get(v___x_49_, 1);
lean_dec(v_unused_65_);
v___x_55_ = v___x_49_;
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_diag_53_);
lean_inc(v_postponed_52_);
lean_inc(v_zetaDeltaFVarIds_51_);
lean_inc(v_mctx_50_);
lean_dec(v___x_49_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_mctx_50_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_zetaDeltaFVarIds_51_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v_postponed_52_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v_diag_53_);
v___x_60_ = v_reuseFailAlloc_63_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_st_ref_put(v___y_25_, v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_57_);
return v___x_62_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___boxed(lean_object* v_ext_69_, lean_object* v_b_70_, lean_object* v_kind_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v_kind_boxed_76_; lean_object* v_res_77_; 
v_kind_boxed_76_ = lean_unbox(v_kind_71_);
v_res_77_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_69_, v_b_70_, v_kind_boxed_76_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_00_u03c3_80_, lean_object* v_ext_81_, lean_object* v_b_82_, uint8_t v_kind_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_81_, v_b_82_, v_kind_83_, v___y_85_, v___y_86_, v___y_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___boxed(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_00_u03c3_92_, lean_object* v_ext_93_, lean_object* v_b_94_, lean_object* v_kind_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
uint8_t v_kind_boxed_101_; lean_object* v_res_102_; 
v_kind_boxed_101_ = lean_unbox(v_kind_95_);
v_res_102_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(v_00_u03b1_90_, v_00_u03b2_91_, v_00_u03c3_92_, v_ext_93_, v_b_94_, v_kind_boxed_101_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_env_110_; uint8_t v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v_toCold_114_; lean_object* v_mctx_115_; lean_object* v_lctx_116_; lean_object* v_options_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_env_110_);
lean_dec(v___x_109_);
v___x_111_ = 0;
v_env_112_ = l_Lean_Environment_setRecordingDeps(v_env_110_, v___x_111_);
v___x_113_ = lean_st_ref_get(v___y_105_);
v_toCold_114_ = lean_ctor_get(v___y_106_, 0);
v_mctx_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_mctx_115_);
lean_dec(v___x_113_);
v_lctx_116_ = lean_ctor_get(v___y_104_, 2);
v_options_117_ = lean_ctor_get(v_toCold_114_, 2);
lean_inc_ref(v_options_117_);
lean_inc_ref(v_lctx_116_);
v___x_118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_118_, 0, v_env_112_);
lean_ctor_set(v___x_118_, 1, v_mctx_115_);
lean_ctor_set(v___x_118_, 2, v_lctx_116_);
lean_ctor_set(v___x_118_, 3, v_options_117_);
v___x_119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_msgData_103_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3___boxed(lean_object* v_msgData_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(v_msgData_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_ref_134_; lean_object* v___x_135_; lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_ref_134_ = lean_ctor_get(v___y_131_, 2);
v___x_135_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(v_msg_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_144_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_ref_134_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_ref_134_);
lean_ctor_set(v___x_140_, 1, v_a_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
lean_ctor_set(v___x_138_, 0, v___x_140_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg___boxed(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(lean_object* v_ext_152_, uint8_t v_post_153_, uint8_t v_a_154_, uint8_t v_attrKind_155_, lean_object* v_prio_156_, lean_object* v_as_157_, size_t v_sz_158_, size_t v_i_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_dec(v_prio_156_);
lean_dec_ref(v_ext_152_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v_b_160_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v_a_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v_a_169_ = lean_array_uget_borrowed(v_as_157_, v_i_159_);
lean_inc(v_prio_156_);
lean_inc(v_a_169_);
lean_inc_ref(v_ext_152_);
v___x_170_ = l_Lean_Meta_addSimpTheorem(v_ext_152_, v_a_169_, v_post_153_, v_a_154_, v_attrKind_155_, v_prio_156_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_170_) == 0)
{
size_t v___x_171_; size_t v___x_172_; 
lean_dec_ref_known(v___x_170_, 1);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_add(v_i_159_, v___x_171_);
v_i_159_ = v___x_172_;
v_b_160_ = v___x_168_;
goto _start;
}
else
{
lean_dec(v_prio_156_);
lean_dec_ref(v_ext_152_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1___boxed(lean_object* v_ext_174_, lean_object* v_post_175_, lean_object* v_a_176_, lean_object* v_attrKind_177_, lean_object* v_prio_178_, lean_object* v_as_179_, lean_object* v_sz_180_, lean_object* v_i_181_, lean_object* v_b_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v_post_boxed_188_; uint8_t v_a_3827__boxed_189_; uint8_t v_attrKind_boxed_190_; size_t v_sz_boxed_191_; size_t v_i_boxed_192_; lean_object* v_res_193_; 
v_post_boxed_188_ = lean_unbox(v_post_175_);
v_a_3827__boxed_189_ = lean_unbox(v_a_176_);
v_attrKind_boxed_190_ = lean_unbox(v_attrKind_177_);
v_sz_boxed_191_ = lean_unbox_usize(v_sz_180_);
lean_dec(v_sz_180_);
v_i_boxed_192_ = lean_unbox_usize(v_i_181_);
lean_dec(v_i_181_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_174_, v_post_boxed_188_, v_a_3827__boxed_189_, v_attrKind_boxed_190_, v_prio_178_, v_as_179_, v_sz_boxed_191_, v_i_boxed_192_, v_b_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec_ref(v_as_179_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__1));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__4(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__3));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__6(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__5));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__7(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__6, &l_Lean_Meta_addDeclToUnfold___closed__6_once, _init_l_Lean_Meta_addDeclToUnfold___closed__6);
v___x_207_ = l_Lean_MessageData_note(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold(lean_object* v_ext_208_, lean_object* v_declName_209_, uint8_t v_post_210_, uint8_t v_inv_211_, lean_object* v_prio_212_, uint8_t v_attrKind_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_env_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; 
v___x_219_ = lean_st_ref_get(v_a_217_);
v_env_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_env_220_);
lean_dec(v___x_219_);
lean_inc(v_declName_209_);
v___x_221_ = l_Lean_getOriginalConstKind_x3f(v_env_220_, v_declName_209_);
v___x_222_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__0));
v___x_223_ = l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
if (v___x_223_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_prio_212_);
lean_dec(v_declName_209_);
lean_dec_ref(v_ext_208_);
v___x_317_ = lean_box(v___x_223_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
else
{
if (v_inv_211_ == 0)
{
v___y_225_ = v_a_214_;
v___y_226_ = v_a_215_;
v___y_227_ = v_a_216_;
v___y_228_ = v_a_217_;
goto v___jp_224_;
}
else
{
lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v_prio_212_);
lean_dec_ref(v_ext_208_);
v___x_319_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__2, &l_Lean_Meta_addDeclToUnfold___closed__2_once, _init_l_Lean_Meta_addDeclToUnfold___closed__2);
v___x_320_ = 0;
v___x_321_ = l_Lean_MessageData_ofConstName(v_declName_209_, v___x_320_);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_319_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__4, &l_Lean_Meta_addDeclToUnfold___closed__4_once, _init_l_Lean_Meta_addDeclToUnfold___closed__4);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__7, &l_Lean_Meta_addDeclToUnfold___closed__7_once, _init_l_Lean_Meta_addDeclToUnfold___closed__7);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_326_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
v___jp_224_:
{
lean_object* v___x_229_; 
lean_inc(v_declName_209_);
v___x_229_ = l_Lean_Meta_Simp_ignoreEquations(v_declName_209_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_316_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_316_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_316_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_316_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_unbox(v_a_230_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_inc(v_declName_209_);
v___x_235_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_209_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
if (lean_obj_tag(v_a_236_) == 1)
{
lean_object* v_val_237_; lean_object* v___x_238_; size_t v_sz_239_; size_t v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
lean_del_object(v___x_232_);
v_val_237_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v_a_236_, 1);
v___x_238_ = lean_box(0);
v_sz_239_ = lean_array_size(v_val_237_);
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_unbox(v_a_230_);
lean_dec(v_a_230_);
lean_inc_ref(v_ext_208_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_208_, v_post_210_, v___x_241_, v_attrKind_213_, v_prio_212_, v_val_237_, v_sz_239_, v___x_240_, v___x_238_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref_known(v___x_242_, 1);
lean_inc(v_declName_209_);
v___x_243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_243_, 0, v_declName_209_);
lean_ctor_set(v___x_243_, 1, v_val_237_);
lean_inc_ref(v_ext_208_);
v___x_244_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_208_, v___x_243_, v_attrKind_213_, v___y_226_, v___y_227_, v___y_228_);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_244_, 0);
lean_dec(v_unused_273_);
v___x_246_ = v___x_244_;
v_isShared_247_ = v_isSharedCheck_272_;
goto v_resetjp_245_;
}
else
{
lean_dec(v___x_244_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_272_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; 
lean_inc(v_declName_209_);
v___x_248_ = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(v_declName_209_, v___y_228_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_271_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_271_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_271_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_271_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
uint8_t v___x_253_; 
v___x_253_ = lean_unbox(v_a_249_);
lean_dec(v_a_249_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_del_object(v___x_246_);
lean_dec(v_declName_209_);
lean_dec_ref(v_ext_208_);
v___x_254_ = lean_box(v___x_223_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_254_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
else
{
lean_object* v___x_259_; 
lean_del_object(v___x_251_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 1);
lean_ctor_set(v___x_246_, 0, v_declName_209_);
v___x_259_ = v___x_246_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_declName_209_);
v___x_259_ = v_reuseFailAlloc_270_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v___x_260_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_208_, v___x_259_, v_attrKind_213_, v___y_226_, v___y_227_, v___y_228_);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; 
v_unused_269_ = lean_ctor_get(v___x_260_, 0);
lean_dec(v_unused_269_);
v___x_262_ = v___x_260_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_dec(v___x_260_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_box(v___x_223_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
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
}
}
else
{
lean_del_object(v___x_246_);
lean_dec(v_declName_209_);
lean_dec_ref(v_ext_208_);
return v___x_248_;
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_val_237_);
lean_dec(v_declName_209_);
lean_dec_ref(v_ext_208_);
v_a_274_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_242_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_242_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v_a_236_);
lean_dec(v_a_230_);
lean_dec(v_prio_212_);
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 1);
lean_ctor_set(v___x_232_, 0, v_declName_209_);
v___x_283_ = v___x_232_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_declName_209_);
v___x_283_ = v_reuseFailAlloc_294_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v___x_284_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_208_, v___x_283_, v_attrKind_213_, v___y_226_, v___y_227_, v___y_228_);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v___x_284_, 0);
lean_dec(v_unused_293_);
v___x_286_ = v___x_284_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_dec(v___x_284_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_box(v___x_223_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_del_object(v___x_232_);
lean_dec(v_a_230_);
lean_dec(v_prio_212_);
lean_dec(v_declName_209_);
lean_dec_ref(v_ext_208_);
v_a_295_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_235_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_235_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v___x_304_; 
lean_dec(v_a_230_);
lean_dec(v_prio_212_);
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 1);
lean_ctor_set(v___x_232_, 0, v_declName_209_);
v___x_304_ = v___x_232_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_declName_209_);
v___x_304_ = v_reuseFailAlloc_315_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v___x_305_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_208_, v___x_304_, v_attrKind_213_, v___y_226_, v___y_227_, v___y_228_);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_305_, 0);
lean_dec(v_unused_314_);
v___x_307_ = v___x_305_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_dec(v___x_305_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_box(v___x_223_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
else
{
lean_dec(v_prio_212_);
lean_dec(v_declName_209_);
lean_dec_ref(v_ext_208_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold___boxed(lean_object* v_ext_336_, lean_object* v_declName_337_, lean_object* v_post_338_, lean_object* v_inv_339_, lean_object* v_prio_340_, lean_object* v_attrKind_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_post_boxed_347_; uint8_t v_inv_boxed_348_; uint8_t v_attrKind_boxed_349_; lean_object* v_res_350_; 
v_post_boxed_347_ = lean_unbox(v_post_338_);
v_inv_boxed_348_ = lean_unbox(v_inv_339_);
v_attrKind_boxed_349_ = lean_unbox(v_attrKind_341_);
v_res_350_ = l_Lean_Meta_addDeclToUnfold(v_ext_336_, v_declName_337_, v_post_boxed_347_, v_inv_boxed_348_, v_prio_340_, v_attrKind_boxed_349_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(lean_object* v_00_u03b1_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___boxed(lean_object* v_00_u03b1_359_, lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(v_00_u03b1_359_, v_msg_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__10));
v___x_394_ = l_Lean_mkAtom(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__12, &l_Lean_Meta_mkSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12);
v___x_396_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_397_ = lean_array_push(v___x_396_, v___x_395_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__17));
v___x_407_ = l_Lean_mkAtom(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__18, &l_Lean_Meta_mkSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18);
v___x_409_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_410_ = lean_array_push(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__19, &l_Lean_Meta_mkSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19);
v___x_412_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__16));
v___x_413_ = lean_box(2);
v___x_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_411_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__20, &l_Lean_Meta_mkSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20);
v___x_416_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__13, &l_Lean_Meta_mkSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13);
v___x_417_ = lean_array_push(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__21, &l_Lean_Meta_mkSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21);
v___x_419_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__11));
v___x_420_ = lean_box(2);
v___x_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_418_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__22, &l_Lean_Meta_mkSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22);
v___x_423_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_424_ = lean_array_push(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__23, &l_Lean_Meta_mkSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23);
v___x_426_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__9));
v___x_427_ = lean_box(2);
v___x_428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_425_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__24, &l_Lean_Meta_mkSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24);
v___x_430_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_431_ = lean_array_push(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__25, &l_Lean_Meta_mkSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25);
v___x_433_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__7));
v___x_434_ = lean_box(2);
v___x_435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_432_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__26, &l_Lean_Meta_mkSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26);
v___x_437_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_438_ = lean_array_push(v___x_437_, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__27, &l_Lean_Meta_mkSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27);
v___x_440_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__4));
v___x_441_ = lean_box(2);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_439_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_446_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_ctor_set(v___x_449_, 2, v___x_448_);
lean_ctor_set(v___x_449_, 3, v___x_448_);
lean_ctor_set(v___x_449_, 4, v___x_447_);
lean_ctor_set(v___x_449_, 5, v___x_447_);
lean_ctor_set(v___x_449_, 6, v___x_447_);
lean_ctor_set(v___x_449_, 7, v___x_447_);
lean_ctor_set(v___x_449_, 8, v___x_447_);
lean_ctor_set(v___x_449_, 9, v___x_447_);
lean_ctor_set(v___x_449_, 10, v___x_447_);
lean_ctor_set(v___x_449_, 11, v___x_446_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3(void){
_start:
{
size_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((size_t)5ULL);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_unsigned_to_nat(32u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
v___x_458_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_454_);
lean_ctor_set(v___x_458_, 3, v___x_454_);
lean_ctor_set_usize(v___x_458_, 4, v___x_453_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_box(1);
v___x_460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_459_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_msg_484_, lean_object* v_declHint_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_env_490_; uint8_t v___x_491_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_st_ref_get(v___y_486_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_env_490_);
lean_dec(v___x_489_);
v___x_491_ = l_Lean_Name_isAnonymous(v_declHint_485_);
if (v___x_491_ == 0)
{
uint8_t v_isExporting_492_; 
v_isExporting_492_ = lean_ctor_get_uint8(v_env_490_, sizeof(void*)*13);
if (v_isExporting_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec_ref(v_env_490_);
lean_dec(v_declHint_485_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_msg_484_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
lean_inc_ref(v_env_490_);
v___x_494_ = l_Lean_Environment_setExporting(v_env_490_, v___x_491_);
lean_inc(v_declHint_485_);
lean_inc_ref(v___x_494_);
v___x_495_ = l_Lean_Environment_contains(v___x_494_, v_declHint_485_, v_isExporting_492_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec_ref(v___x_494_);
lean_dec_ref(v_env_490_);
lean_dec(v_declHint_485_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_msg_484_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_c_502_; lean_object* v___x_503_; 
v___x_497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
v___x_498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_499_ = l_Lean_Options_empty;
v___x_500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_500_, 0, v___x_494_);
lean_ctor_set(v___x_500_, 1, v___x_497_);
lean_ctor_set(v___x_500_, 2, v___x_498_);
lean_ctor_set(v___x_500_, 3, v___x_499_);
lean_inc(v_declHint_485_);
v___x_501_ = l_Lean_MessageData_ofConstName(v_declHint_485_, v___x_491_);
v_c_502_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_502_, 0, v___x_500_);
lean_ctor_set(v_c_502_, 1, v___x_501_);
v___x_503_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_490_, v_declHint_485_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref(v_env_490_);
lean_dec(v_declHint_485_);
v___x_504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_c_502_);
v___x_506_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = l_Lean_MessageData_note(v___x_507_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v_msg_484_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_545_; 
v_val_511_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_545_ == 0)
{
v___x_513_ = v___x_503_;
v_isShared_514_ = v_isSharedCheck_545_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_val_511_);
lean_dec(v___x_503_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_545_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v_moduleNames_516_; lean_object* v_mod_517_; uint8_t v___x_518_; 
v___x_515_ = l_Lean_Environment_header(v_env_490_);
lean_dec_ref(v_env_490_);
v_moduleNames_516_ = lean_ctor_get(v___x_515_, 4);
lean_inc_ref(v_moduleNames_516_);
lean_dec_ref(v___x_515_);
v_mod_517_ = lean_array_get(v___x_488_, v_moduleNames_516_, v_val_511_);
lean_dec(v_val_511_);
lean_dec_ref(v_moduleNames_516_);
v___x_518_ = l_Lean_isPrivateName(v_declHint_485_);
lean_dec(v_declHint_485_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_c_502_);
v___x_521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_MessageData_ofName(v_mod_517_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_MessageData_note(v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v_msg_484_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 0);
lean_ctor_set(v___x_513_, 0, v___x_528_);
v___x_530_ = v___x_513_;
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
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_c_502_);
v___x_534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_MessageData_ofName(v_mod_517_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_MessageData_note(v___x_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v_msg_484_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 0);
lean_ctor_set(v___x_513_, 0, v___x_541_);
v___x_543_ = v___x_513_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
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
}
}
}
else
{
lean_object* v___x_546_; 
lean_dec_ref(v_env_490_);
lean_dec(v_declHint_485_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v_msg_484_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_msg_547_, lean_object* v_declHint_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_547_, v_declHint_548_, v___y_549_);
lean_dec(v___y_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_msg_552_, lean_object* v_declHint_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v___x_559_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_552_, v_declHint_553_, v___y_557_);
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = l_Lean_unknownIdentifierMessageTag;
v___x_565_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v_a_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msg_570_, lean_object* v_declHint_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_570_, v_declHint_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_ref_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_toCold_585_; lean_object* v_currRecDepth_586_; lean_object* v_ref_587_; uint16_t v_optionFlags_588_; uint8_t v_suppressElabErrors_589_; uint8_t v_isRecordingDeps_590_; lean_object* v_ref_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_toCold_585_ = lean_ctor_get(v___y_582_, 0);
v_currRecDepth_586_ = lean_ctor_get(v___y_582_, 1);
v_ref_587_ = lean_ctor_get(v___y_582_, 2);
v_optionFlags_588_ = lean_ctor_get_uint16(v___y_582_, sizeof(void*)*3);
v_suppressElabErrors_589_ = lean_ctor_get_uint8(v___y_582_, sizeof(void*)*3 + 2);
v_isRecordingDeps_590_ = lean_ctor_get_uint8(v___y_582_, sizeof(void*)*3 + 3);
v_ref_591_ = l_Lean_replaceRef(v_ref_578_, v_ref_587_);
lean_inc(v_currRecDepth_586_);
lean_inc_ref(v_toCold_585_);
v___x_592_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_592_, 0, v_toCold_585_);
lean_ctor_set(v___x_592_, 1, v_currRecDepth_586_);
lean_ctor_set(v___x_592_, 2, v_ref_591_);
lean_ctor_set_uint16(v___x_592_, sizeof(void*)*3, v_optionFlags_588_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3 + 2, v_suppressElabErrors_589_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3 + 3, v_isRecordingDeps_590_);
v___x_593_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_579_, v___y_580_, v___y_581_, v___x_592_, v___y_583_);
lean_dec_ref_known(v___x_592_, 3);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_ref_594_, lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_594_, v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v_ref_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_602_, lean_object* v_msg_603_, lean_object* v_declHint_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; lean_object* v_a_611_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_603_, v_declHint_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref(v___x_610_);
v___x_612_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_602_, v_a_611_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_613_, lean_object* v_msg_614_, lean_object* v_declHint_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_613_, v_msg_614_, v_declHint_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v_ref_613_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_628_, lean_object* v_constName_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_635_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_636_ = 0;
lean_inc(v_constName_629_);
v___x_637_ = l_Lean_MessageData_ofConstName(v_constName_629_, v___x_636_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_628_, v___x_640_, v_constName_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_642_, lean_object* v_constName_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_642_, v_constName_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v_ref_642_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object* v_constName_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_ref_656_; lean_object* v___x_657_; 
v_ref_656_ = lean_ctor_get(v___y_653_, 2);
v___x_657_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_656_, v_constName_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_constName_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object* v_constName_665_, uint8_t v_skipRealize_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_env_673_; lean_object* v___x_674_; 
v___x_672_ = lean_st_ref_get(v___y_670_);
v_env_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_env_673_);
lean_dec(v___x_672_);
lean_inc(v_constName_665_);
v___x_674_ = l_Lean_Environment_findAsync_x3f(v_env_673_, v_constName_665_, v_skipRealize_666_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_665_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
return v___x_675_;
}
else
{
lean_object* v_val_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_constName_665_);
v_val_676_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_674_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_val_676_);
lean_dec(v___x_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 0);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_val_676_);
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
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object* v_constName_684_, lean_object* v_skipRealize_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_skipRealize_boxed_691_; lean_object* v_res_692_; 
v_skipRealize_boxed_691_ = lean_unbox(v_skipRealize_685_);
v_res_692_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_constName_684_, v_skipRealize_boxed_691_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_692_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_695_ = lean_box(1);
v___x_696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_697_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
lean_ctor_set(v___x_698_, 2, v___x_695_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_702_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
lean_ctor_set(v___x_704_, 3, v___x_703_);
lean_ctor_set(v___x_704_, 4, v___x_702_);
lean_ctor_set(v___x_704_, 5, v___x_702_);
lean_ctor_set(v___x_704_, 6, v___x_702_);
lean_ctor_set(v___x_704_, 7, v___x_702_);
lean_ctor_set(v___x_704_, 8, v___x_702_);
lean_ctor_set(v___x_704_, 9, v___x_702_);
lean_ctor_set(v___x_704_, 10, v___x_702_);
lean_ctor_set(v___x_704_, 11, v___x_701_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_706_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_ctor_set(v___x_706_, 3, v___x_705_);
lean_ctor_set(v___x_706_, 4, v___x_705_);
lean_ctor_set(v___x_706_, 5, v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
lean_ctor_set(v___x_708_, 2, v___x_707_);
lean_ctor_set(v___x_708_, 3, v___x_707_);
lean_ctor_set(v___x_708_, 4, v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__6));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__8));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__10));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__11, &l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11);
v___x_719_ = l_Lean_MessageData_note(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object* v_attrName_726_, lean_object* v___x_727_, lean_object* v_ext_728_, lean_object* v_declName_729_, lean_object* v_stx_730_, uint8_t v_attrKind_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v_declName_729_);
v___x_738_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_729_, v___y_733_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_unbox(v_a_739_);
lean_dec(v_a_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_729_, v___y_733_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_857_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_857_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_857_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_857_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint8_t v___x_746_; 
v___x_746_ = lean_unbox(v_a_742_);
if (v___x_746_ == 0)
{
uint8_t v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; uint8_t v___x_753_; uint8_t v___x_754_; uint8_t v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; uint8_t v___x_758_; uint64_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; uint8_t v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___y_782_; uint8_t v___x_783_; lean_object* v___x_784_; 
lean_dec(v_attrName_726_);
v___x_747_ = 1;
v___x_748_ = 1;
v___x_749_ = 0;
v___x_750_ = 2;
v___x_751_ = lean_alloc_ctor(0, 0, 20);
v___x_752_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 0, v___x_752_);
v___x_753_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 1, v___x_753_);
v___x_754_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 2, v___x_754_);
v___x_755_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 3, v___x_755_);
v___x_756_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 4, v___x_756_);
lean_ctor_set_uint8(v___x_751_, 5, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 6, v___x_747_);
v___x_757_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 7, v___x_757_);
lean_ctor_set_uint8(v___x_751_, 8, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 9, v___x_748_);
lean_ctor_set_uint8(v___x_751_, 10, v___x_749_);
lean_ctor_set_uint8(v___x_751_, 11, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 12, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 13, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 14, v___x_750_);
lean_ctor_set_uint8(v___x_751_, 15, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 16, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 17, v___x_747_);
lean_ctor_set_uint8(v___x_751_, 18, v___x_747_);
v___x_758_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_751_, 19, v___x_758_);
v___x_759_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_751_);
v___x_760_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_760_, 0, v___x_751_);
lean_ctor_set_uint64(v___x_760_, sizeof(void*)*1, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_763_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__1, &l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1);
v___x_764_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__2));
v___x_765_ = lean_box(0);
lean_inc(v___x_727_);
v___x_766_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_766_, 0, v___x_760_);
lean_ctor_set(v___x_766_, 1, v___x_727_);
lean_ctor_set(v___x_766_, 2, v___x_763_);
lean_ctor_set(v___x_766_, 3, v___x_764_);
lean_ctor_set(v___x_766_, 4, v___x_765_);
lean_ctor_set(v___x_766_, 5, v___x_761_);
lean_ctor_set(v___x_766_, 6, v___x_765_);
v___x_767_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*7, v___x_767_);
v___x_768_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*7 + 1, v___x_768_);
v___x_769_ = lean_unbox(v_a_742_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*7 + 2, v___x_769_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*7 + 3, v___x_747_);
v___x_770_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_771_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__4, &l_Lean_Meta_mkSimpAttr___lam__0___closed__4_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4);
v___x_772_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__5, &l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5);
v___x_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_773_, 0, v___x_770_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
lean_ctor_set(v___x_773_, 2, v___x_727_);
lean_ctor_set(v___x_773_, 3, v___x_762_);
lean_ctor_set(v___x_773_, 4, v___x_772_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_st_mk_ref(v___x_773_);
v___x_783_ = lean_unbox(v_a_742_);
lean_inc(v_declName_729_);
v___x_784_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_declName_729_, v___x_783_, v___x_766_, v___x_775_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; uint8_t v___y_787_; uint8_t v___y_788_; uint8_t v___y_837_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_842_);
v___x_844_ = l_Lean_Syntax_isNone(v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_845_ = l_Lean_Syntax_getArg(v___x_843_, v___x_761_);
lean_dec(v___x_843_);
v___x_846_ = l_Lean_Syntax_getKind(v___x_845_);
v___x_847_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__14));
v___x_848_ = lean_name_eq(v___x_846_, v___x_847_);
lean_dec(v___x_846_);
v___y_837_ = v___x_848_;
goto v___jp_836_;
}
else
{
lean_dec(v___x_843_);
v___y_837_ = v___x_747_;
goto v___jp_836_;
}
v___jp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_unsigned_to_nat(3u);
v___x_790_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_789_);
lean_dec(v_stx_730_);
v___x_791_ = l_Lean_getAttrParamOptPrio(v___x_790_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_sig_793_; lean_object* v___x_794_; lean_object* v_type_795_; lean_object* v___x_796_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_sig_793_ = lean_ctor_get(v_a_785_, 1);
lean_inc_ref(v_sig_793_);
lean_dec(v_a_785_);
v___x_794_ = lean_task_get_own(v_sig_793_);
v_type_795_ = lean_ctor_get(v___x_794_, 2);
lean_inc_ref(v_type_795_);
lean_dec(v___x_794_);
v___x_796_ = l_Lean_Meta_isProp(v_type_795_, v___x_766_, v___x_775_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; uint8_t v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = lean_unbox(v_a_797_);
lean_dec(v_a_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_inc(v_declName_729_);
v___x_799_ = l_Lean_Meta_addDeclToUnfold(v_ext_728_, v_declName_729_, v___y_787_, v___y_788_, v_a_792_, v_attrKind_731_, v___x_766_, v___x_775_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; uint8_t v___x_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = lean_unbox(v_a_800_);
lean_dec(v_a_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_802_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__7, &l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7);
v___x_803_ = lean_unbox(v_a_742_);
lean_dec(v_a_742_);
v___x_804_ = l_Lean_MessageData_ofConstName(v_declName_729_, v___x_803_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_802_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__9, &l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__12, &l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_809_, v___x_766_, v___x_775_, v___y_732_, v___y_733_);
lean_dec_ref_known(v___x_766_, 7);
v___y_782_ = v___x_810_;
goto v___jp_781_;
}
else
{
lean_dec_ref_known(v___x_766_, 7);
lean_dec(v_a_742_);
lean_dec(v_declName_729_);
goto v___jp_776_;
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v___x_775_);
lean_dec_ref_known(v___x_766_, 7);
lean_del_object(v___x_744_);
lean_dec(v_a_742_);
lean_dec(v_declName_729_);
v_a_811_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_799_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_799_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v_a_742_);
v___x_819_ = l_Lean_Meta_addSimpTheorem(v_ext_728_, v_declName_729_, v___y_787_, v___y_788_, v_attrKind_731_, v_a_792_, v___x_766_, v___x_775_, v___y_732_, v___y_733_);
lean_dec_ref_known(v___x_766_, 7);
v___y_782_ = v___x_819_;
goto v___jp_781_;
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_a_792_);
lean_dec(v___x_775_);
lean_dec_ref_known(v___x_766_, 7);
lean_del_object(v___x_744_);
lean_dec(v_a_742_);
lean_dec(v_declName_729_);
lean_dec_ref(v_ext_728_);
v_a_820_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_796_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_796_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_a_785_);
lean_dec(v___x_775_);
lean_dec_ref_known(v___x_766_, 7);
lean_del_object(v___x_744_);
lean_dec(v_a_742_);
lean_dec(v_declName_729_);
lean_dec_ref(v_ext_728_);
v_a_828_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_791_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_791_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(2u);
v___x_839_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_838_);
v___x_840_ = l_Lean_Syntax_isNone(v___x_839_);
lean_dec(v___x_839_);
if (v___x_840_ == 0)
{
v___y_787_ = v___y_837_;
v___y_788_ = v___x_747_;
goto v___jp_786_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = lean_unbox(v_a_742_);
v___y_787_ = v___y_837_;
v___y_788_ = v___x_841_;
goto v___jp_786_;
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v___x_775_);
lean_dec_ref_known(v___x_766_, 7);
lean_del_object(v___x_744_);
lean_dec(v_a_742_);
lean_dec(v_stx_730_);
lean_dec(v_declName_729_);
lean_dec_ref(v_ext_728_);
v_a_849_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_784_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_784_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
v___jp_776_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_st_ref_get(v___x_775_);
lean_dec(v___x_775_);
lean_dec(v___x_777_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_774_);
v___x_779_ = v___x_744_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
v___jp_781_:
{
if (lean_obj_tag(v___y_782_) == 0)
{
lean_dec_ref_known(v___y_782_, 1);
goto v___jp_776_;
}
else
{
lean_dec(v___x_775_);
lean_del_object(v___x_744_);
return v___y_782_;
}
}
}
else
{
lean_del_object(v___x_744_);
lean_dec(v_a_742_);
lean_dec_ref(v_ext_728_);
lean_dec(v___x_727_);
goto v___jp_735_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_stx_730_);
lean_dec(v_declName_729_);
lean_dec_ref(v_ext_728_);
lean_dec(v___x_727_);
lean_dec(v_attrName_726_);
v_a_858_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_741_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_741_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_dec_ref(v_ext_728_);
lean_dec(v___x_727_);
goto v___jp_735_;
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_stx_730_);
lean_dec(v_declName_729_);
lean_dec_ref(v_ext_728_);
lean_dec(v___x_727_);
lean_dec(v_attrName_726_);
v_a_866_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_738_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_738_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
v___jp_735_:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_726_);
v___x_737_ = l_Lean_Attribute_add(v_declName_729_, v___x_736_, v_stx_730_, v_attrKind_731_, v___y_732_, v___y_733_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object* v_attrName_874_, lean_object* v___x_875_, lean_object* v_ext_876_, lean_object* v_declName_877_, lean_object* v_stx_878_, lean_object* v_attrKind_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v_attrKind_boxed_883_; lean_object* v_res_884_; 
v_attrKind_boxed_883_ = lean_unbox(v_attrKind_879_);
v_res_884_ = l_Lean_Meta_mkSimpAttr___lam__0(v_attrName_874_, v___x_875_, v_ext_876_, v_declName_877_, v_stx_878_, v_attrKind_boxed_883_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object* v_a_885_, lean_object* v_x_886_){
_start:
{
lean_inc_ref(v_a_885_);
return v_a_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object* v_a_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_mkSimpAttr___lam__1(v_a_887_, v_x_888_);
lean_dec_ref(v_x_888_);
lean_dec_ref(v_a_887_);
return v_res_889_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_keys_890_, lean_object* v_i_891_, lean_object* v_k_892_){
_start:
{
lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = lean_array_get_size(v_keys_890_);
v___x_894_ = lean_nat_dec_lt(v_i_891_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec(v_i_891_);
return v___x_894_;
}
else
{
lean_object* v_k_x27_895_; uint8_t v___x_896_; 
v_k_x27_895_ = lean_array_fget_borrowed(v_keys_890_, v_i_891_);
v___x_896_ = lean_name_eq(v_k_892_, v_k_x27_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_add(v_i_891_, v___x_897_);
lean_dec(v_i_891_);
v_i_891_ = v___x_898_;
goto _start;
}
else
{
lean_dec(v_i_891_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_keys_900_, lean_object* v_i_901_, lean_object* v_k_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_900_, v_i_901_, v_k_902_);
lean_dec(v_k_902_);
lean_dec_ref(v_keys_900_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(lean_object* v_x_905_, size_t v_x_906_, lean_object* v_x_907_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v_es_908_; lean_object* v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v_j_912_; lean_object* v___x_913_; 
v_es_908_ = lean_ctor_get(v_x_905_, 0);
v___x_909_ = lean_box(2);
v___x_910_ = ((size_t)31ULL);
v___x_911_ = lean_usize_land(v_x_906_, v___x_910_);
v_j_912_ = lean_usize_to_nat(v___x_911_);
v___x_913_ = lean_array_get_borrowed(v___x_909_, v_es_908_, v_j_912_);
lean_dec(v_j_912_);
switch(lean_obj_tag(v___x_913_))
{
case 0:
{
lean_object* v_key_914_; uint8_t v___x_915_; 
v_key_914_ = lean_ctor_get(v___x_913_, 0);
v___x_915_ = lean_name_eq(v_x_907_, v_key_914_);
return v___x_915_;
}
case 1:
{
lean_object* v_node_916_; size_t v___x_917_; size_t v___x_918_; 
v_node_916_ = lean_ctor_get(v___x_913_, 0);
v___x_917_ = ((size_t)5ULL);
v___x_918_ = lean_usize_shift_right(v_x_906_, v___x_917_);
v_x_905_ = v_node_916_;
v_x_906_ = v___x_918_;
goto _start;
}
default: 
{
uint8_t v___x_920_; 
v___x_920_ = 0;
return v___x_920_;
}
}
}
else
{
lean_object* v_ks_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_ks_921_ = lean_ctor_get(v_x_905_, 0);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_ks_921_, v___x_922_, v_x_907_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
size_t v_x_9007__boxed_927_; uint8_t v_res_928_; lean_object* v_r_929_; 
v_x_9007__boxed_927_ = lean_unbox_usize(v_x_925_);
lean_dec(v_x_925_);
v_res_928_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_924_, v_x_9007__boxed_927_, v_x_926_);
lean_dec(v_x_926_);
lean_dec_ref(v_x_924_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
uint64_t v___y_933_; 
if (lean_obj_tag(v_x_931_) == 0)
{
uint64_t v___x_936_; 
v___x_936_ = 1723ULL;
v___y_933_ = v___x_936_;
goto v___jp_932_;
}
else
{
uint64_t v_hash_937_; 
v_hash_937_ = lean_ctor_get_uint64(v_x_931_, sizeof(void*)*2);
v___y_933_ = v_hash_937_;
goto v___jp_932_;
}
v___jp_932_:
{
size_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_uint64_to_usize(v___y_933_);
v___x_935_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_930_, v___x_934_, v_x_931_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___boxed(lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_938_, v_x_939_);
lean_dec(v_x_939_);
lean_dec_ref(v_x_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_msgData_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v_toCold_947_; lean_object* v_env_948_; lean_object* v_options_949_; uint8_t v___x_950_; lean_object* v_env_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_946_ = lean_st_ref_get(v___y_944_);
v_toCold_947_ = lean_ctor_get(v___y_943_, 0);
v_env_948_ = lean_ctor_get(v___x_946_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_946_);
v_options_949_ = lean_ctor_get(v_toCold_947_, 2);
v___x_950_ = 0;
v_env_951_ = l_Lean_Environment_setRecordingDeps(v_env_948_, v___x_950_);
v___x_952_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
v___x_953_ = lean_unsigned_to_nat(32u);
v___x_954_ = lean_mk_empty_array_with_capacity(v___x_953_);
lean_dec_ref(v___x_954_);
v___x_955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
lean_inc_ref(v_options_949_);
v___x_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_956_, 0, v_env_951_);
lean_ctor_set(v___x_956_, 1, v___x_952_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v_options_949_);
v___x_957_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_msgData_942_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(uint8_t v_suppressElabErrors_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_972_) == 1)
{
lean_object* v_pre_973_; 
v_pre_973_ = lean_ctor_get(v_x_972_, 0);
switch(lean_obj_tag(v_pre_973_))
{
case 1:
{
lean_object* v_pre_974_; 
v_pre_974_ = lean_ctor_get(v_pre_973_, 0);
switch(lean_obj_tag(v_pre_974_))
{
case 0:
{
lean_object* v_str_975_; lean_object* v_str_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_str_975_ = lean_ctor_get(v_x_972_, 1);
v_str_976_ = lean_ctor_get(v_pre_973_, 1);
v___x_977_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0));
v___x_978_ = lean_string_dec_eq(v_str_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__2));
v___x_980_ = lean_string_dec_eq(v_str_976_, v___x_979_);
if (v___x_980_ == 0)
{
return v___x_980_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1));
v___x_982_ = lean_string_dec_eq(v_str_975_, v___x_981_);
if (v___x_982_ == 0)
{
return v___x_982_;
}
else
{
return v_suppressElabErrors_971_;
}
}
}
else
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2));
v___x_984_ = lean_string_dec_eq(v_str_975_, v___x_983_);
if (v___x_984_ == 0)
{
return v___x_984_;
}
else
{
return v_suppressElabErrors_971_;
}
}
}
case 1:
{
lean_object* v_pre_985_; 
v_pre_985_ = lean_ctor_get(v_pre_974_, 0);
if (lean_obj_tag(v_pre_985_) == 0)
{
lean_object* v_str_986_; lean_object* v_str_987_; lean_object* v_str_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v_str_986_ = lean_ctor_get(v_x_972_, 1);
v_str_987_ = lean_ctor_get(v_pre_973_, 1);
v_str_988_ = lean_ctor_get(v_pre_974_, 1);
v___x_989_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3));
v___x_990_ = lean_string_dec_eq(v_str_988_, v___x_989_);
if (v___x_990_ == 0)
{
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4));
v___x_992_ = lean_string_dec_eq(v_str_987_, v___x_991_);
if (v___x_992_ == 0)
{
return v___x_992_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5));
v___x_994_ = lean_string_dec_eq(v_str_986_, v___x_993_);
if (v___x_994_ == 0)
{
return v___x_994_;
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
uint8_t v___x_995_; 
v___x_995_ = 0;
return v___x_995_;
}
}
default: 
{
uint8_t v___x_996_; 
v___x_996_ = 0;
return v___x_996_;
}
}
}
case 0:
{
lean_object* v_str_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_str_997_ = lean_ctor_get(v_x_972_, 1);
v___x_998_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6));
v___x_999_ = lean_string_dec_eq(v_str_997_, v___x_998_);
if (v___x_999_ == 0)
{
return v___x_999_;
}
else
{
return v_suppressElabErrors_971_;
}
}
default: 
{
uint8_t v___x_1000_; 
v___x_1000_ = 0;
return v___x_1000_;
}
}
}
else
{
uint8_t v___x_1001_; 
v___x_1001_ = 0;
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1004_; uint8_t v_res_1005_; lean_object* v_r_1006_; 
v_suppressElabErrors_boxed_1004_ = lean_unbox(v_suppressElabErrors_1002_);
v_res_1005_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(v_suppressElabErrors_boxed_1004_, v_x_1003_);
lean_dec(v_x_1003_);
v_r_1006_ = lean_box(v_res_1005_);
return v_r_1006_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(lean_object* v_opts_1007_, lean_object* v_opt_1008_){
_start:
{
lean_object* v_name_1009_; lean_object* v_defValue_1010_; lean_object* v_map_1011_; lean_object* v___x_1012_; 
v_name_1009_ = lean_ctor_get(v_opt_1008_, 0);
v_defValue_1010_ = lean_ctor_get(v_opt_1008_, 1);
v_map_1011_ = lean_ctor_get(v_opts_1007_, 0);
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1011_, v_name_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_unbox(v_defValue_1010_);
return v___x_1013_;
}
else
{
lean_object* v_val_1014_; 
v_val_1014_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v___x_1012_, 1);
if (lean_obj_tag(v_val_1014_) == 1)
{
uint8_t v_v_1015_; 
v_v_1015_ = lean_ctor_get_uint8(v_val_1014_, 0);
lean_dec_ref_known(v_val_1014_, 0);
return v_v_1015_;
}
else
{
uint8_t v___x_1016_; 
lean_dec(v_val_1014_);
v___x_1016_ = lean_unbox(v_defValue_1010_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11___boxed(lean_object* v_opts_1017_, lean_object* v_opt_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_opts_1017_, v_opt_1018_);
lean_dec_ref(v_opt_1018_);
lean_dec_ref(v_opts_1017_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(lean_object* v_ref_1022_, lean_object* v_msgData_1023_, uint8_t v_severity_1024_, uint8_t v_isSilent_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v_toCold_1037_; lean_object* v___y_1038_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; uint8_t v___y_1071_; uint8_t v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1100_; uint8_t v___y_1104_; uint8_t v___y_1105_; uint8_t v___x_1115_; uint8_t v___y_1117_; uint8_t v___x_1123_; 
v___x_1115_ = 2;
v___x_1123_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1024_, v___x_1115_);
if (v___x_1123_ == 0)
{
v___y_1117_ = v___x_1123_;
goto v___jp_1116_;
}
else
{
uint8_t v___x_1124_; 
lean_inc_ref(v_msgData_1023_);
v___x_1124_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1023_);
if (v___x_1124_ == 0)
{
v___y_1117_ = v___x_1124_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec_ref(v_msgData_1023_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
}
v___jp_1029_:
{
lean_object* v_currNamespace_1039_; lean_object* v_openDecls_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_env_1045_; lean_object* v_nextMacroScope_1046_; lean_object* v_ngen_1047_; lean_object* v_auxDeclNGen_1048_; lean_object* v_traceState_1049_; lean_object* v_cache_1050_; lean_object* v_recordedDeps_1051_; lean_object* v_messages_1052_; lean_object* v_infoState_1053_; lean_object* v_snapshotTasks_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1065_; 
v_currNamespace_1039_ = lean_ctor_get(v_toCold_1037_, 4);
v_openDecls_1040_ = lean_ctor_get(v_toCold_1037_, 5);
lean_inc(v_openDecls_1040_);
lean_inc(v_currNamespace_1039_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_currNamespace_1039_);
lean_ctor_set(v___x_1041_, 1, v_openDecls_1040_);
v___x_1042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___y_1031_);
lean_inc_ref(v___y_1033_);
lean_inc_ref(v___y_1030_);
v___x_1043_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1043_, 0, v___y_1030_);
lean_ctor_set(v___x_1043_, 1, v___y_1035_);
lean_ctor_set(v___x_1043_, 2, v___y_1032_);
lean_ctor_set(v___x_1043_, 3, v___y_1033_);
lean_ctor_set(v___x_1043_, 4, v___x_1042_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*5, v___y_1034_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*5 + 1, v___y_1036_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*5 + 2, v_isSilent_1025_);
v___x_1044_ = lean_st_ref_take(v___y_1038_);
v_env_1045_ = lean_ctor_get(v___x_1044_, 0);
v_nextMacroScope_1046_ = lean_ctor_get(v___x_1044_, 1);
v_ngen_1047_ = lean_ctor_get(v___x_1044_, 2);
v_auxDeclNGen_1048_ = lean_ctor_get(v___x_1044_, 3);
v_traceState_1049_ = lean_ctor_get(v___x_1044_, 4);
v_cache_1050_ = lean_ctor_get(v___x_1044_, 5);
v_recordedDeps_1051_ = lean_ctor_get(v___x_1044_, 6);
v_messages_1052_ = lean_ctor_get(v___x_1044_, 7);
v_infoState_1053_ = lean_ctor_get(v___x_1044_, 8);
v_snapshotTasks_1054_ = lean_ctor_get(v___x_1044_, 9);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1056_ = v___x_1044_;
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snapshotTasks_1054_);
lean_inc(v_infoState_1053_);
lean_inc(v_messages_1052_);
lean_inc(v_recordedDeps_1051_);
lean_inc(v_cache_1050_);
lean_inc(v_traceState_1049_);
lean_inc(v_auxDeclNGen_1048_);
lean_inc(v_ngen_1047_);
lean_inc(v_nextMacroScope_1046_);
lean_inc(v_env_1045_);
lean_dec(v___x_1044_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Lean_MessageLog_add(v___x_1043_, v_messages_1052_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 7, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_env_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_nextMacroScope_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_ngen_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_auxDeclNGen_1048_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_traceState_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v_cache_1050_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_recordedDeps_1051_);
lean_ctor_set(v_reuseFailAlloc_1064_, 7, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1064_, 8, v_infoState_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 9, v_snapshotTasks_1054_);
v___x_1061_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_st_ref_put(v___y_1038_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1058_);
return v___x_1063_;
}
}
}
v___jp_1066_:
{
lean_object* v_fileName_1075_; lean_object* v_fileMap_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1092_; 
v_fileName_1075_ = lean_ctor_get(v___y_1073_, 0);
v_fileMap_1076_ = lean_ctor_get(v___y_1073_, 1);
v___x_1077_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1023_);
v___x_1078_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v___x_1077_, v___y_1026_, v___y_1027_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1092_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1092_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc_ref_n(v_fileMap_1076_, 2);
v___x_1083_ = l_Lean_FileMap_toPosition(v_fileMap_1076_, v___y_1069_);
lean_dec(v___y_1069_);
v___x_1084_ = l_Lean_FileMap_toPosition(v_fileMap_1076_, v___y_1074_);
lean_dec(v___y_1074_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
v___x_1086_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0));
if (v___y_1070_ == 0)
{
lean_del_object(v___x_1081_);
lean_dec_ref(v___y_1067_);
v___y_1030_ = v_fileName_1075_;
v___y_1031_ = v_a_1079_;
v___y_1032_ = v___x_1085_;
v___y_1033_ = v___x_1086_;
v___y_1034_ = v___y_1071_;
v___y_1035_ = v___x_1083_;
v___y_1036_ = v___y_1072_;
v_toCold_1037_ = v___y_1068_;
v___y_1038_ = v___y_1027_;
goto v___jp_1029_;
}
else
{
uint8_t v___x_1087_; 
lean_inc(v_a_1079_);
v___x_1087_ = l_Lean_MessageData_hasTag(v___y_1067_, v_a_1079_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec_ref_known(v___x_1085_, 1);
lean_dec_ref(v___x_1083_);
lean_dec(v_a_1079_);
v___x_1088_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1088_);
v___x_1090_ = v___x_1081_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
else
{
lean_del_object(v___x_1081_);
v___y_1030_ = v_fileName_1075_;
v___y_1031_ = v_a_1079_;
v___y_1032_ = v___x_1085_;
v___y_1033_ = v___x_1086_;
v___y_1034_ = v___y_1071_;
v___y_1035_ = v___x_1083_;
v___y_1036_ = v___y_1072_;
v_toCold_1037_ = v___y_1068_;
v___y_1038_ = v___y_1027_;
goto v___jp_1029_;
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Syntax_getTailPos_x3f(v___y_1097_, v___y_1098_);
lean_dec(v___y_1097_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_inc(v___y_1100_);
v___y_1067_ = v___y_1095_;
v___y_1068_ = v___y_1096_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1094_;
v___y_1071_ = v___y_1098_;
v___y_1072_ = v___y_1099_;
v___y_1073_ = v___y_1096_;
v___y_1074_ = v___y_1100_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1102_; 
v_val_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___y_1067_ = v___y_1095_;
v___y_1068_ = v___y_1096_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1094_;
v___y_1071_ = v___y_1098_;
v___y_1072_ = v___y_1099_;
v___y_1073_ = v___y_1096_;
v___y_1074_ = v_val_1102_;
goto v___jp_1066_;
}
}
v___jp_1103_:
{
lean_object* v_toCold_1106_; lean_object* v_ref_1107_; uint8_t v_suppressElabErrors_1108_; lean_object* v___x_1109_; lean_object* v___f_1110_; lean_object* v_ref_1111_; lean_object* v___x_1112_; 
v_toCold_1106_ = lean_ctor_get(v___y_1026_, 0);
v_ref_1107_ = lean_ctor_get(v___y_1026_, 2);
v_suppressElabErrors_1108_ = lean_ctor_get_uint8(v___y_1026_, sizeof(void*)*3 + 2);
v___x_1109_ = lean_box(v_suppressElabErrors_1108_);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1110_, 0, v___x_1109_);
v_ref_1111_ = l_Lean_replaceRef(v_ref_1022_, v_ref_1107_);
v___x_1112_ = l_Lean_Syntax_getPos_x3f(v_ref_1111_, v___y_1104_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___y_1094_ = v_suppressElabErrors_1108_;
v___y_1095_ = v___f_1110_;
v___y_1096_ = v_toCold_1106_;
v___y_1097_ = v_ref_1111_;
v___y_1098_ = v___y_1104_;
v___y_1099_ = v___y_1105_;
v___y_1100_ = v___x_1113_;
goto v___jp_1093_;
}
else
{
lean_object* v_val_1114_; 
v_val_1114_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v___x_1112_, 1);
v___y_1094_ = v_suppressElabErrors_1108_;
v___y_1095_ = v___f_1110_;
v___y_1096_ = v_toCold_1106_;
v___y_1097_ = v_ref_1111_;
v___y_1098_ = v___y_1104_;
v___y_1099_ = v___y_1105_;
v___y_1100_ = v_val_1114_;
goto v___jp_1093_;
}
}
v___jp_1116_:
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 1;
v___x_1119_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1024_, v___x_1118_);
if (v___x_1119_ == 0)
{
v___y_1104_ = v___y_1117_;
v___y_1105_ = v_severity_1024_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1026_);
v___x_1121_ = l_Lean_warningAsError;
v___x_1122_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v___x_1120_, v___x_1121_);
lean_dec_ref(v___x_1120_);
if (v___x_1122_ == 0)
{
v___y_1104_ = v___y_1117_;
v___y_1105_ = v_severity_1024_;
goto v___jp_1103_;
}
else
{
v___y_1104_ = v___y_1117_;
v___y_1105_ = v___x_1115_;
goto v___jp_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_1127_, lean_object* v_msgData_1128_, lean_object* v_severity_1129_, lean_object* v_isSilent_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v_severity_boxed_1134_; uint8_t v_isSilent_boxed_1135_; lean_object* v_res_1136_; 
v_severity_boxed_1134_ = lean_unbox(v_severity_1129_);
v_isSilent_boxed_1135_ = lean_unbox(v_isSilent_1130_);
v_res_1136_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1127_, v_msgData_1128_, v_severity_boxed_1134_, v_isSilent_boxed_1135_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v_ref_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(lean_object* v_msgData_1137_, uint8_t v_severity_1138_, uint8_t v_isSilent_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_ref_1143_; lean_object* v___x_1144_; 
v_ref_1143_ = lean_ctor_get(v___y_1140_, 2);
v___x_1144_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1143_, v_msgData_1137_, v_severity_1138_, v_isSilent_1139_, v___y_1140_, v___y_1141_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1145_, lean_object* v_severity_1146_, lean_object* v_isSilent_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v_severity_boxed_1151_; uint8_t v_isSilent_boxed_1152_; lean_object* v_res_1153_; 
v_severity_boxed_1151_ = lean_unbox(v_severity_1146_);
v_isSilent_boxed_1152_ = lean_unbox(v_isSilent_1147_);
v_res_1153_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1145_, v_severity_boxed_1151_, v_isSilent_boxed_1152_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(lean_object* v_msgData_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = 1;
v___x_1159_ = 0;
v___x_1160_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1154_, v___x_1158_, v___x_1159_, v___y_1155_, v___y_1156_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2___boxed(lean_object* v_msgData_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v_msgData_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object* v_d_1169_, lean_object* v_thmId_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1169_, v_thmId_1170_);
if (v___x_1213_ == 0)
{
if (lean_obj_tag(v_thmId_1170_) == 0)
{
lean_object* v_declName_1214_; uint8_t v___x_1215_; 
v_declName_1214_ = lean_ctor_get(v_thmId_1170_, 0);
v___x_1215_ = l_Lean_Meta_SimpTheorems_isDeclToUnfold(v_d_1169_, v_declName_1214_);
if (v___x_1215_ == 0)
{
lean_object* v_toUnfoldThms_1216_; uint8_t v___x_1217_; 
v_toUnfoldThms_1216_ = lean_ctor_get(v_d_1169_, 5);
v___x_1217_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_toUnfoldThms_1216_, v_declName_1214_);
if (v___x_1217_ == 0)
{
goto v___jp_1201_;
}
else
{
goto v___jp_1174_;
}
}
else
{
goto v___jp_1174_;
}
}
else
{
goto v___jp_1201_;
}
}
else
{
goto v___jp_1174_;
}
v___jp_1174_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1169_, v_thmId_1170_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
v___jp_1177_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1178_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1179_ = l_Lean_Meta_Origin_key(v_thmId_1170_);
lean_dec_ref(v_thmId_1170_);
v___x_1180_ = l_Lean_MessageData_ofName(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1178_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_obj_once(&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1, &l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once, _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v___x_1183_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v___x_1184_, 0);
lean_dec(v_unused_1192_);
v___x_1186_ = v___x_1184_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v___x_1184_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v_d_1169_);
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_d_1169_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_d_1169_);
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1184_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
v___jp_1201_:
{
lean_object* v___x_1202_; 
lean_inc_ref(v_thmId_1170_);
v___x_1202_ = l_Lean_Meta_Origin_converse(v_thmId_1170_);
if (lean_obj_tag(v___x_1202_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1212_; 
v_val_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1212_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_val_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1212_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1169_, v_val_1203_);
if (v___x_1207_ == 0)
{
lean_del_object(v___x_1205_);
lean_dec(v_val_1203_);
goto v___jp_1177_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_dec_ref(v_thmId_1170_);
v___x_1208_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1169_, v_val_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_dec(v___x_1202_);
goto v___jp_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object* v_d_1218_, lean_object* v_thmId_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v_d_1218_, v_thmId_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object* v_attrName_1224_, lean_object* v_ext_1225_, lean_object* v___x_1226_, lean_object* v_declName_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1234_; 
lean_inc(v_declName_1227_);
v___x_1234_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_1227_, v___y_1229_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; uint8_t v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_1227_, v___y_1229_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; uint8_t v___x_1239_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = lean_unbox(v_a_1238_);
if (v___x_1239_ == 0)
{
uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v_ext_1242_; lean_object* v_toEnvExtension_1243_; lean_object* v_env_1244_; lean_object* v_asyncMode_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_attrName_1224_);
v___x_1240_ = 1;
v___x_1241_ = lean_st_ref_get(v___y_1229_);
v_ext_1242_ = lean_ctor_get(v_ext_1225_, 1);
v_toEnvExtension_1243_ = lean_ctor_get(v_ext_1242_, 0);
v_env_1244_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_env_1244_);
lean_dec(v___x_1241_);
v_asyncMode_1245_ = lean_ctor_get(v_toEnvExtension_1243_, 2);
v___x_1246_ = lean_unbox(v_a_1238_);
v___x_1247_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1226_, v_ext_1225_, v_env_1244_, v_asyncMode_1245_, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1248_, 0, v_declName_1227_);
lean_ctor_set_uint8(v___x_1248_, sizeof(void*)*1, v___x_1240_);
v___x_1249_ = lean_unbox(v_a_1238_);
lean_dec(v_a_1238_);
lean_ctor_set_uint8(v___x_1248_, sizeof(void*)*1 + 1, v___x_1249_);
v___x_1250_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v___x_1247_, v___x_1248_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1281_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1281_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1281_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v_env_1257_; lean_object* v_nextMacroScope_1258_; lean_object* v_ngen_1259_; lean_object* v_auxDeclNGen_1260_; lean_object* v_traceState_1261_; lean_object* v_recordedDeps_1262_; lean_object* v_messages_1263_; lean_object* v_infoState_1264_; lean_object* v_snapshotTasks_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1279_; 
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1255_, 0, v_a_1251_);
v___x_1256_ = lean_st_ref_take(v___y_1229_);
v_env_1257_ = lean_ctor_get(v___x_1256_, 0);
v_nextMacroScope_1258_ = lean_ctor_get(v___x_1256_, 1);
v_ngen_1259_ = lean_ctor_get(v___x_1256_, 2);
v_auxDeclNGen_1260_ = lean_ctor_get(v___x_1256_, 3);
v_traceState_1261_ = lean_ctor_get(v___x_1256_, 4);
v_recordedDeps_1262_ = lean_ctor_get(v___x_1256_, 6);
v_messages_1263_ = lean_ctor_get(v___x_1256_, 7);
v_infoState_1264_ = lean_ctor_get(v___x_1256_, 8);
v_snapshotTasks_1265_ = lean_ctor_get(v___x_1256_, 9);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1256_, 5);
lean_dec(v_unused_1280_);
v___x_1267_ = v___x_1256_;
v_isShared_1268_ = v_isSharedCheck_1279_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snapshotTasks_1265_);
lean_inc(v_infoState_1264_);
lean_inc(v_messages_1263_);
lean_inc(v_recordedDeps_1262_);
lean_inc(v_traceState_1261_);
lean_inc(v_auxDeclNGen_1260_);
lean_inc(v_ngen_1259_);
lean_inc(v_nextMacroScope_1258_);
lean_inc(v_env_1257_);
lean_dec(v___x_1256_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1279_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1225_, v_env_1257_, v___f_1255_);
v___x_1271_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 5, v___x_1271_);
lean_ctor_set(v___x_1267_, 0, v___x_1270_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_nextMacroScope_1258_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_ngen_1259_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_auxDeclNGen_1260_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_traceState_1261_);
lean_ctor_set(v_reuseFailAlloc_1278_, 5, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1278_, 6, v_recordedDeps_1262_);
lean_ctor_set(v_reuseFailAlloc_1278_, 7, v_messages_1263_);
lean_ctor_set(v_reuseFailAlloc_1278_, 8, v_infoState_1264_);
lean_ctor_set(v_reuseFailAlloc_1278_, 9, v_snapshotTasks_1265_);
v___x_1273_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_st_ref_put(v___y_1229_, v___x_1273_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1269_);
v___x_1276_ = v___x_1253_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1269_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_ext_1225_);
v_a_1282_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1250_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1250_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_dec(v_a_1238_);
lean_dec_ref(v_ext_1225_);
goto v___jp_1231_;
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_declName_1227_);
lean_dec_ref(v_ext_1225_);
lean_dec(v_attrName_1224_);
v_a_1290_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1237_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1237_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_dec_ref(v_ext_1225_);
goto v___jp_1231_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_declName_1227_);
lean_dec_ref(v_ext_1225_);
lean_dec(v_attrName_1224_);
v_a_1298_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1234_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1234_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
v___jp_1231_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_1224_);
v___x_1233_ = l_Lean_Attribute_erase(v_declName_1227_, v___x_1232_, v___y_1228_, v___y_1229_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object* v_attrName_1306_, lean_object* v_ext_1307_, lean_object* v___x_1308_, lean_object* v_declName_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Meta_mkSimpAttr___lam__2(v_attrName_1306_, v_ext_1307_, v___x_1308_, v_declName_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v___x_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* v_attrName_1314_, lean_object* v_attrDescr_1315_, lean_object* v_ext_1316_, lean_object* v_ref_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1319_ = lean_box(1);
lean_inc_ref(v_ext_1316_);
lean_inc_n(v_attrName_1314_, 2);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1320_, 0, v_attrName_1314_);
lean_closure_set(v___f_1320_, 1, v___x_1319_);
lean_closure_set(v___f_1320_, 2, v_ext_1316_);
v___x_1321_ = l_Lean_Meta_instInhabitedSimpTheorems_default;
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1322_, 0, v_attrName_1314_);
lean_closure_set(v___f_1322_, 1, v_ext_1316_);
lean_closure_set(v___f_1322_, 2, v___x_1321_);
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
size_t v_x_9739__boxed_1385_; uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_x_9739__boxed_1385_ = lean_unbox_usize(v_x_1383_);
lean_dec(v_x_1383_);
v_res_1386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(v_00_u03b2_1381_, v_x_1382_, v_x_9739__boxed_1385_, v_x_1384_);
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
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_nbuckets_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1520_ = lean_array_get_size(v_data_1519_);
v___x_1521_ = lean_unsigned_to_nat(2u);
v_nbuckets_1522_ = lean_nat_mul(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_mk_array(v_nbuckets_1522_, v___x_1524_);
v___x_1526_ = lean_array_propagate_mark(v_data_1519_, v___x_1525_);
v___x_1527_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_1523_, v_data_1519_, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_1528_, lean_object* v_x_1529_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = 0;
return v___x_1530_;
}
else
{
lean_object* v_key_1531_; lean_object* v_tail_1532_; uint8_t v___x_1533_; 
v_key_1531_ = lean_ctor_get(v_x_1529_, 0);
v_tail_1532_ = lean_ctor_get(v_x_1529_, 2);
v___x_1533_ = lean_name_eq(v_key_1531_, v_a_1528_);
if (v___x_1533_ == 0)
{
v_x_1529_ = v_tail_1532_;
goto _start;
}
else
{
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_1535_, lean_object* v_x_1536_){
_start:
{
uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_res_1537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1535_, v_x_1536_);
lean_dec(v_x_1536_);
lean_dec(v_a_1535_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(lean_object* v_m_1539_, lean_object* v_a_1540_, lean_object* v_b_1541_){
_start:
{
lean_object* v_size_1542_; lean_object* v_buckets_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1589_; 
v_size_1542_ = lean_ctor_get(v_m_1539_, 0);
v_buckets_1543_ = lean_ctor_get(v_m_1539_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_m_1539_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1545_ = v_m_1539_;
v_isShared_1546_ = v_isSharedCheck_1589_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_buckets_1543_);
lean_inc(v_size_1542_);
lean_dec(v_m_1539_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1589_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; uint64_t v___y_1549_; 
v___x_1547_ = lean_array_get_size(v_buckets_1543_);
if (lean_obj_tag(v_a_1540_) == 0)
{
uint64_t v___x_1587_; 
v___x_1587_ = 1723ULL;
v___y_1549_ = v___x_1587_;
goto v___jp_1548_;
}
else
{
uint64_t v_hash_1588_; 
v_hash_1588_ = lean_ctor_get_uint64(v_a_1540_, sizeof(void*)*2);
v___y_1549_ = v_hash_1588_;
goto v___jp_1548_;
}
v___jp_1548_:
{
uint64_t v___x_1550_; uint64_t v___x_1551_; uint64_t v_fold_1552_; uint64_t v___x_1553_; uint64_t v___x_1554_; uint64_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; lean_object* v_bkt_1561_; uint8_t v___x_1562_; 
v___x_1550_ = 32ULL;
v___x_1551_ = lean_uint64_shift_right(v___y_1549_, v___x_1550_);
v_fold_1552_ = lean_uint64_xor(v___y_1549_, v___x_1551_);
v___x_1553_ = 16ULL;
v___x_1554_ = lean_uint64_shift_right(v_fold_1552_, v___x_1553_);
v___x_1555_ = lean_uint64_xor(v_fold_1552_, v___x_1554_);
v___x_1556_ = lean_uint64_to_usize(v___x_1555_);
v___x_1557_ = lean_usize_of_nat(v___x_1547_);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_sub(v___x_1557_, v___x_1558_);
v___x_1560_ = lean_usize_land(v___x_1556_, v___x_1559_);
v_bkt_1561_ = lean_array_uget_borrowed(v_buckets_1543_, v___x_1560_);
v___x_1562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1540_, v_bkt_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v_size_x27_1564_; lean_object* v___x_1565_; lean_object* v_buckets_x27_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
v_size_x27_1564_ = lean_nat_add(v_size_1542_, v___x_1563_);
lean_dec(v_size_1542_);
lean_inc(v_bkt_1561_);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1540_);
lean_ctor_set(v___x_1565_, 1, v_b_1541_);
lean_ctor_set(v___x_1565_, 2, v_bkt_1561_);
v_buckets_x27_1566_ = lean_array_uset(v_buckets_1543_, v___x_1560_, v___x_1565_);
v___x_1567_ = lean_unsigned_to_nat(4u);
v___x_1568_ = lean_nat_mul(v_size_x27_1564_, v___x_1567_);
v___x_1569_ = lean_unsigned_to_nat(3u);
v___x_1570_ = lean_nat_div(v___x_1568_, v___x_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_array_get_size(v_buckets_x27_1566_);
v___x_1572_ = lean_nat_dec_le(v___x_1570_, v___x_1571_);
lean_dec(v___x_1570_);
if (v___x_1572_ == 0)
{
lean_object* v_val_1573_; lean_object* v___x_1575_; 
v_val_1573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_1566_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_val_1573_);
lean_ctor_set(v___x_1545_, 0, v_size_x27_1564_);
v___x_1575_ = v___x_1545_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_size_x27_1564_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_val_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v___x_1578_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_buckets_x27_1566_);
lean_ctor_set(v___x_1545_, 0, v_size_x27_1564_);
v___x_1578_ = v___x_1545_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_size_x27_1564_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_buckets_x27_1566_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v_buckets_x27_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_inc(v_bkt_1561_);
v___x_1580_ = lean_box(0);
v_buckets_x27_1581_ = lean_array_uset(v_buckets_1543_, v___x_1560_, v___x_1580_);
v___x_1582_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1540_, v_b_1541_, v_bkt_1561_);
v___x_1583_ = lean_array_uset(v_buckets_x27_1581_, v___x_1560_, v___x_1582_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v___x_1583_);
v___x_1585_ = v___x_1545_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_size_1542_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* v_attrName_1590_, lean_object* v_attrDescr_1591_, lean_object* v_ref_1592_){
_start:
{
lean_object* v___x_1594_; 
lean_inc(v_ref_1592_);
v___x_1594_ = l_Lean_Meta_mkSimpExt(v_ref_1592_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc_n(v_a_1595_, 2);
lean_dec_ref_known(v___x_1594_, 1);
lean_inc(v_attrName_1590_);
v___x_1596_ = l_Lean_Meta_mkSimpAttr(v_attrName_1590_, v_attrDescr_1591_, v_a_1595_, v_ref_1592_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1608_);
v___x_1598_ = v___x_1596_;
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v___x_1596_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1600_ = l_Lean_Meta_simpExtensionMapRef;
v___x_1601_ = lean_st_ref_take(v___x_1600_);
lean_inc(v_a_1595_);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v___x_1601_, v_attrName_1590_, v_a_1595_);
v___x_1603_ = lean_st_ref_put(v___x_1600_, v___x_1602_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_a_1595_);
v___x_1605_ = v___x_1598_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1595_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_a_1595_);
lean_dec(v_attrName_1590_);
v_a_1609_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1596_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1596_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_dec(v_ref_1592_);
lean_dec_ref(v_attrDescr_1591_);
lean_dec(v_attrName_1590_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___boxed(lean_object* v_attrName_1617_, lean_object* v_attrDescr_1618_, lean_object* v_ref_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_registerSimpAttr(v_attrName_1617_, v_attrDescr_1618_, v_ref_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(lean_object* v_00_u03b2_1622_, lean_object* v_m_1623_, lean_object* v_a_1624_, lean_object* v_b_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v_m_1623_, v_a_1624_, v_b_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_1627_, lean_object* v_a_1628_, lean_object* v_x_1629_){
_start:
{
uint8_t v___x_1630_; 
v___x_1630_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1628_, v_x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_a_1632_, lean_object* v_x_1633_){
_start:
{
uint8_t v_res_1634_; lean_object* v_r_1635_; 
v_res_1634_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(v_00_u03b2_1631_, v_a_1632_, v_x_1633_);
lean_dec(v_x_1633_);
lean_dec(v_a_1632_);
v_r_1635_ = lean_box(v_res_1634_);
return v_r_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_1636_, lean_object* v_data_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_data_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_b_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1640_, v_b_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1644_, lean_object* v_i_1645_, lean_object* v_source_1646_, lean_object* v_target_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_1645_, v_source_1646_, v_target_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1650_, v_x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1667_ = l_Lean_Meta_registerSimpAttr(v___x_1664_, v___x_1665_, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1683_ = l_Lean_Meta_registerSimpAttr(v___x_1680_, v___x_1681_, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = l_Lean_Meta_simpExtension;
v___x_1689_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1688_, v_a_1686_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1690_);
lean_dec(v_a_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Meta_getSimpTheorems(v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = l_Lean_Meta_sevalSimpExtension;
v___x_1704_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1703_, v_a_1701_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1705_);
lean_dec(v_a_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_getSEvalTheorems(v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1725_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1725_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = ((lean_object*)(l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0));
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_mk_empty_array_with_capacity(v___x_1732_);
v___x_1734_ = lean_array_push(v___x_1733_, v_a_1728_);
v___x_1735_ = l_Lean_Options_empty;
v___x_1736_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1731_, v___x_1734_, v_a_1730_, v___x_1735_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1736_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_a_1728_);
v_a_1737_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1729_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1729_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1727_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1727_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1758_, v_a_1760_, v_a_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Meta_Simp_Context_mkDefault(v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1769_;
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
